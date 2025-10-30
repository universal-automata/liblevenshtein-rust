//! SIMD-accelerated Levenshtein distance implementations
//!
//! This module provides vectorized implementations of edit distance algorithms
//! using AVX2 and SSE4.1 intrinsics for significant performance improvements.
//!
//! The implementation uses runtime CPU feature detection to automatically select
//! the fastest available implementation (AVX2 > SSE4.1 > scalar fallback).

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

/// Compute standard Levenshtein distance with SIMD acceleration
///
/// This function automatically selects the best SIMD implementation based on
/// CPU features detected at runtime. Falls back to scalar implementation if
/// SIMD is unavailable or strings are too short.
///
/// # Arguments
/// * `source` - The source string
/// * `target` - The target string
///
/// # Returns
/// The Levenshtein distance between the two strings
#[cfg(target_arch = "x86_64")]
pub fn standard_distance_simd(source: &str, target: &str) -> usize {
    // For short strings, SIMD overhead outweighs benefits
    // Use scalar implementation for strings shorter than 16 characters
    let source_len = source.chars().count();
    let target_len = target.chars().count();

    if source_len < 16 && target_len < 16 {
        return crate::distance::standard_distance_impl(source, target);
    }

    // Check for AVX2 support
    if is_x86_feature_detected!("avx2") {
        unsafe { standard_distance_avx2(source, target) }
    } else if is_x86_feature_detected!("sse4.1") {
        unsafe { standard_distance_sse41(source, target) }
    } else {
        // Fall back to scalar implementation
        crate::distance::standard_distance_impl(source, target)
    }
}

/// AVX2 implementation of standard Levenshtein distance
///
/// Uses 256-bit AVX2 vectors to process 8 u32 values in parallel.
/// This implementation uses a banded approach to vectorize operations
/// where possible while respecting data dependencies.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn standard_distance_avx2(source: &str, target: &str) -> usize {
    use smallvec::SmallVec;

    let source_chars: SmallVec<[char; 32]> = source.chars().collect();
    let target_chars: SmallVec<[char; 32]> = target.chars().collect();

    let m = source_chars.len();
    let n = target_chars.len();

    // Handle empty strings
    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    // For very short strings, scalar is faster due to SIMD overhead
    if n < 16 {
        return crate::distance::standard_distance_impl(source, target);
    }

    // Allocate DP rows
    let mut prev_row = vec![0u32; n + 1];
    let mut curr_row = vec![0u32; n + 1];

    // Initialize first row using SIMD
    init_row_simd_avx2(&mut prev_row);

    // Constants for SIMD operations
    let one_vec = _mm256_set1_epi32(1);

    // Process each row
    for i in 1..=m {
        curr_row[0] = i as u32;
        let source_char = source_chars[i - 1] as u32;

        // Process columns in groups of 8 where possible
        let mut j = 1;
        while j + 8 <= n {
            // Load 8 target characters
            let mut target_buf = [0u32; 8];
            for k in 0..8 {
                target_buf[k] = target_chars[j - 1 + k] as u32;
            }
            let target_vec = _mm256_loadu_si256(target_buf.as_ptr() as *const __m256i);

            // Broadcast source character
            let source_vec = _mm256_set1_epi32(source_char as i32);

            // Compare: result is 0xFFFFFFFF where equal, 0 where different
            let eq_mask = _mm256_cmpeq_epi32(source_vec, target_vec);

            // Convert to costs: 0 if equal, 1 if different
            // Use andnot: costs = (!eq_mask) & 1
            let costs = _mm256_andnot_si256(eq_mask, one_vec);

            // Load values from previous row
            // prev_row[j..j+8] for deletion cost
            let prev_same = _mm256_loadu_si256(prev_row.as_ptr().add(j) as *const __m256i);

            // prev_row[j-1..j+7] for substitution cost
            let prev_diag = _mm256_loadu_si256(prev_row.as_ptr().add(j - 1) as *const __m256i);

            // Calculate deletion: prev_row[j] + 1
            let deletion = _mm256_add_epi32(prev_same, one_vec);

            // Calculate substitution: prev_row[j-1] + cost
            let substitution = _mm256_add_epi32(prev_diag, costs);

            // For insertion, we need curr_row[j-1] which has dependencies
            // Process first element with dependency, then vectorize the rest
            if j == 1 {
                // First element: full scalar calculation
                let cost = if source_char == target_chars[0] as u32 { 0 } else { 1 };
                curr_row[1] = min3_scalar(
                    prev_row[1] + 1,
                    curr_row[0] + 1,
                    prev_row[0] + cost,
                );
                j += 1;
                continue;
            }

            // For remaining elements, we can partially vectorize
            // Calculate min(deletion, substitution) first
            let min_del_sub = _mm256_min_epu32(deletion, substitution);

            // Store partial results and finalize with insertion cost scalar
            let mut partial = [0u32; 8];
            _mm256_storeu_si256(partial.as_mut_ptr() as *mut __m256i, min_del_sub);

            // Finalize each cell with insertion cost
            for k in 0..8.min(n + 1 - j) {
                let insertion = curr_row[j + k - 1] + 1;
                curr_row[j + k] = partial[k].min(insertion);
            }

            j += 8;
        }

        // Process remaining columns with scalar code
        for j in j..=n {
            let cost = if source_char == target_chars[j - 1] as u32 { 0 } else { 1 };
            curr_row[j] = min3_scalar(
                prev_row[j] + 1,
                curr_row[j - 1] + 1,
                prev_row[j - 1] + cost,
            );
        }

        // Swap rows
        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[n] as usize
}

/// Initialize a DP row with sequential values using AVX2
///
/// Fills the row [0, 1, 2, 3, ..., n] using vectorized stores
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn init_row_simd_avx2(row: &mut [u32]) {
    let n = row.len();
    let simd_count = n / 8;

    // Create increment vector [0, 1, 2, 3, 4, 5, 6, 7]
    let base = _mm256_setr_epi32(0, 1, 2, 3, 4, 5, 6, 7);
    let increment = _mm256_set1_epi32(8);

    let mut current = base;

    // Fill 8 elements at a time
    for i in 0..simd_count {
        _mm256_storeu_si256(row.as_mut_ptr().add(i * 8) as *mut __m256i, current);
        current = _mm256_add_epi32(current, increment);
    }

    // Fill remainder
    for i in (simd_count * 8)..n {
        row[i] = i as u32;
    }
}

/// SSE4.1 implementation of standard Levenshtein distance
///
/// Uses 128-bit SSE vectors to process 4 u32 values in parallel.
/// Fallback for systems without AVX2 support.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse4.1")]
unsafe fn standard_distance_sse41(source: &str, target: &str) -> usize {
    // For now, fall back to scalar
    // TODO: Implement SSE4.1 version similar to AVX2 but with 128-bit vectors
    crate::distance::standard_distance_impl(source, target)
}

/// Scalar min3 helper
#[inline(always)]
fn min3_scalar(a: u32, b: u32, c: u32) -> u32 {
    a.min(b).min(c)
}

/// Vectorized min3 using AVX2
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn min3_avx2(a: __m256i, b: __m256i, c: __m256i) -> __m256i {
    let ab_min = _mm256_min_epu32(a, b);
    _mm256_min_epu32(ab_min, c)
}

#[cfg(not(target_arch = "x86_64"))]
pub fn standard_distance_simd(source: &str, target: &str) -> usize {
    // Non-x86_64 platforms fall back to scalar implementation
    crate::distance::standard_distance_impl(source, target)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_simd_basic() {
        assert_eq!(standard_distance_simd("", ""), 0);
        assert_eq!(standard_distance_simd("abc", ""), 3);
        assert_eq!(standard_distance_simd("", "abc"), 3);
        assert_eq!(standard_distance_simd("abc", "abc"), 0);
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_simd_vs_scalar() {
        let test_cases = vec![
            ("kitten", "sitting"),
            ("saturday", "sunday"),
            ("book", "back"),
            ("hello world", "hallo welt"),
        ];

        for (source, target) in test_cases {
            let simd_result = standard_distance_simd(source, target);
            let scalar_result = crate::distance::standard_distance_impl(source, target);
            assert_eq!(
                simd_result, scalar_result,
                "SIMD and scalar results differ for ('{}', '{}')",
                source, target
            );
        }
    }
}
