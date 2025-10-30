//! Simple prototype to test pulp SIMD functionality
//!
//! This demonstrates basic pulp usage for vectorized operations.
//! Run with: cargo run --example simd_prototype --features simd

#[cfg(feature = "simd")]
use pulp::Arch;

fn main() {
    #[cfg(feature = "simd")]
    {
        println!("Testing pulp SIMD functionality...\n");

        // Detect available CPU features
        let arch = Arch::new();
        println!("CPU Architecture detected: {:?}", arch);
        println!("Available SIMD features:");
        println!("  - Has AVX2: {}", cfg!(target_feature = "avx2"));
        println!("  - Has SSE2: {}", cfg!(target_feature = "sse2"));
        println!("\n");

        // Test simple vectorized addition
        test_vectorized_add();

        // Test vectorized minimum (relevant for Levenshtein)
        test_vectorized_min();
    }

    #[cfg(not(feature = "simd"))]
    {
        println!("SIMD feature not enabled!");
        println!("Run with: cargo run --example simd_prototype --features simd");
    }
}

#[cfg(feature = "simd")]
fn test_vectorized_add() {
    use pulp::{Arch, Simd, WithSimd};

    println!("=== Test 1: Vectorized Addition ===");

    struct VectorAdd {
        a: [u32; 8],
        b: [u32; 8],
        result: [u32; 8],
    }

    impl WithSimd for VectorAdd {
        type Output = [u32; 8];

        #[inline(always)]
        fn with_simd<S: Simd>(mut self, simd: S) -> Self::Output {
            // Simple scalar addition for now (pulp u32 operations are more complex)
            for i in 0..8 {
                self.result[i] = self.a[i] + self.b[i];
            }
            self.result
        }
    }

    let arch = Arch::new();
    let a = [1u32, 2, 3, 4, 5, 6, 7, 8];
    let b = [8u32, 7, 6, 5, 4, 3, 2, 1];
    let result = arch.dispatch(VectorAdd {
        a,
        b,
        result: [0u32; 8],
    });

    println!("Input A:  {:?}", a);
    println!("Input B:  {:?}", b);
    println!("Sum:      {:?}", result);
    println!("Expected: [9, 9, 9, 9, 9, 9, 9, 9]\n");
}

#[cfg(feature = "simd")]
fn test_vectorized_min() {
    use pulp::{Arch, Simd, WithSimd};

    println!("=== Test 2: Vectorized Minimum (for DP) ===");

    struct VectorMin {
        deletion: [u32; 8],
        insertion: [u32; 8],
        substitution: [u32; 8],
    }

    impl WithSimd for VectorMin {
        type Output = [u32; 8];

        #[inline(always)]
        fn with_simd<S: Simd>(self, _simd: S) -> Self::Output {
            let mut result = [0u32; 8];
            // Compute min3 for each element
            for i in 0..8 {
                result[i] = self.deletion[i]
                    .min(self.insertion[i])
                    .min(self.substitution[i]);
            }
            result
        }
    }

    let arch = Arch::new();

    // Simulate three DP options: deletion, insertion, substitution
    let deletion = [5u32, 8, 3, 9, 2, 7, 4, 6];
    let insertion = [6u32, 7, 4, 8, 3, 6, 5, 7];
    let substitution = [4u32, 9, 2, 7, 4, 5, 6, 8];

    let min_result = arch.dispatch(VectorMin {
        deletion,
        insertion,
        substitution,
    });

    println!("Deletion:     {:?}", deletion);
    println!("Insertion:    {:?}", insertion);
    println!("Substitution: {:?}", substitution);
    println!("Min:          {:?}", min_result);
    println!("Expected:     [4, 7, 2, 7, 2, 5, 4, 6]");

    // Verify correctness
    let expected = [4u32, 7, 2, 7, 2, 5, 4, 6];
    let correct = min_result == expected;
    println!("Correct: {}\n", correct);
}
