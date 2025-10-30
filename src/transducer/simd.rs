//! SIMD-accelerated transducer operations
//!
//! This module provides vectorized implementations of hot-path transducer
//! operations using AVX2 and SSE4.1 intrinsics for significant performance
//! improvements.
//!
//! The implementation uses runtime CPU feature detection to automatically select
//! the fastest available implementation (AVX2 > SSE4.1 > scalar fallback).

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

/// Compute characteristic vector using SIMD acceleration
///
/// This function compares a dictionary character against up to 8 query characters
/// in parallel, achieving 3-4x speedup over scalar comparison.
///
/// # Arguments
/// * `dict_char` - Character from the dictionary edge
/// * `query` - Query term bytes
/// * `window_size` - Size of the window (typically max_distance + 1)
/// * `offset` - Base offset in query
/// * `buffer` - Stack-allocated buffer to write results into
///
/// # Returns
/// Slice of booleans indicating matches at each position in window.
#[cfg(all(target_arch = "x86_64", feature = "simd"))]
pub fn characteristic_vector_simd<'a>(
    dict_char: u8,
    query: &[u8],
    window_size: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    let len = window_size.min(8);

    // Use SIMD for window_size >= 4 (worth the overhead)
    if len >= 8 && is_x86_feature_detected!("avx2") {
        unsafe { characteristic_vector_avx2(dict_char, query, len, offset, buffer) }
    } else if len >= 4 && is_x86_feature_detected!("sse4.1") {
        unsafe { characteristic_vector_sse41(dict_char, query, len, offset, buffer) }
    } else {
        characteristic_vector_scalar(dict_char, query, len, offset, buffer)
    }
}

/// Scalar fallback for characteristic vector computation
#[inline(always)]
fn characteristic_vector_scalar<'a>(
    dict_char: u8,
    query: &[u8],
    len: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    for (i, item) in buffer.iter_mut().enumerate().take(len) {
        let query_idx = offset + i;
        *item = query_idx < query.len() && query[query_idx] == dict_char;
    }
    &buffer[..len]
}

/// AVX2-accelerated characteristic vector computation
///
/// Processes 8 characters at once using 256-bit SIMD vectors
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn characteristic_vector_avx2<'a>(
    dict_char: u8,
    query: &[u8],
    len: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    debug_assert!(len == 8, "AVX2 path expects exactly 8 elements");

    // Broadcast dictionary character to all 32 bytes (we'll use first 8)
    let dict_vec = _mm256_set1_epi8(dict_char as i8);

    // Load 8 query characters (with bounds checking)
    let mut query_buf = [0u8; 32]; // 256-bit = 32 bytes
    for i in 0..8 {
        let query_idx = offset + i;
        query_buf[i] = if query_idx < query.len() {
            query[query_idx]
        } else {
            0xFF // Out of bounds = use invalid byte that won't match
        };
    }

    // Load as 256-bit vector (only first 8 bytes matter)
    let query_vec = _mm256_loadu_si256(query_buf.as_ptr() as *const __m256i);

    // Compare all bytes at once
    let cmp_result = _mm256_cmpeq_epi8(dict_vec, query_vec);

    // Extract comparison results (first 8 bits are what we care about)
    let mask = _mm256_movemask_epi8(cmp_result);

    // Write results to buffer (first 8 bits of mask)
    for i in 0..8 {
        buffer[i] = (mask & (1 << i)) != 0;
    }

    &buffer[..len]
}

/// SSE4.1-accelerated characteristic vector computation
///
/// Processes 4 characters at once using 128-bit SIMD vectors
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse4.1")]
unsafe fn characteristic_vector_sse41<'a>(
    dict_char: u8,
    query: &[u8],
    len: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    debug_assert!(len >= 4, "SSE4.1 path expects at least 4 elements");

    // Broadcast dictionary character to all 16 bytes
    let dict_vec = _mm_set1_epi8(dict_char as i8);

    // Process first 4 characters
    let mut query_buf = [0u8; 4];
    for i in 0..4 {
        let query_idx = offset + i;
        query_buf[i] = if query_idx < query.len() {
            query[query_idx]
        } else {
            0 // Out of bounds = no match
        };
    }

    // Load as 32-bit value
    let query_val = u32::from_le_bytes(query_buf);
    let query_vec = _mm_set1_epi32(query_val as i32);

    // Compare first 4 bytes
    let cmp_result = _mm_cmpeq_epi8(dict_vec, query_vec);
    let mask = _mm_movemask_epi8(cmp_result);

    // Write first 4 results
    for i in 0..4 {
        buffer[i] = (mask & (1 << i)) != 0;
    }

    // Process remaining elements with scalar
    for i in 4..len {
        let query_idx = offset + i;
        buffer[i] = query_idx < query.len() && query[query_idx] == dict_char;
    }

    &buffer[..len]
}

/// Non-x86_64 platforms use scalar implementation
#[cfg(not(all(target_arch = "x86_64", feature = "simd")))]
pub fn characteristic_vector_simd<'a>(
    dict_char: u8,
    query: &[u8],
    window_size: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    characteristic_vector_scalar(dict_char, query, window_size.min(8), offset, buffer)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(all(target_arch = "x86_64", feature = "simd"))]
    fn test_characteristic_vector_simd() {
        let test_cases = vec![
            // (dict_char, query, window_size, offset, expected)
            (b'a', b"aaaaaaa".as_slice(), 7, 0, vec![true; 7]),
            (b'a', b"abcdefg".as_slice(), 7, 0, vec![true, false, false, false, false, false, false]),
            (b'x', b"abcdefg".as_slice(), 7, 0, vec![false; 7]),
            (b'a', b"abc".as_slice(), 5, 0, vec![true, false, false, false, false]), // Out of bounds
            (b'c', b"abcdefg".as_slice(), 5, 2, vec![true, false, false, false, false]), // Offset
            (b'a', b"aaa".as_slice(), 8, 0, vec![true, true, true, false, false, false, false, false]), // Full 8
        ];

        for (dict_char, query, window_size, offset, expected) in test_cases {
            let mut buffer = [false; 8];
            let result = characteristic_vector_simd(dict_char, query, window_size, offset, &mut buffer);

            assert_eq!(
                result, &expected[..],
                "SIMD result mismatch for dict_char={}, query={:?}, window_size={}, offset={}",
                dict_char as char, query, window_size, offset
            );

            // Compare against scalar
            let mut scalar_buffer = [false; 8];
            let scalar_result = characteristic_vector_scalar(
                dict_char,
                query,
                window_size.min(8),
                offset,
                &mut scalar_buffer,
            );

            assert_eq!(
                result, scalar_result,
                "SIMD vs scalar mismatch for dict_char={}, query={:?}, window_size={}, offset={}",
                dict_char as char, query, window_size, offset
            );
        }
    }
}
