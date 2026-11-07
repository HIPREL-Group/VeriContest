use vstd::prelude::*;

verus! {

/// Constructs a permutation of [0, n) from the identity permutation, then
/// optionally applies a single swap controlled by `mutation_kind`.
///
/// Construction parameters:
///   n            – length of the permutation (1..=100_000)
///   swap_i       – first swap position  (< n)
///   swap_j       – second swap position (< n)
///   mutation_kind – 0 = identity (no swap), otherwise apply swap(swap_i, swap_j)
pub fn generate_test_case(
    n: usize,
    swap_i: usize,
    swap_j: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= n <= 100_000,
        swap_i < n,
        swap_j < n,
    ensures
        1 <= result.len() <= 100_000,
        forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] < result.len(),
        forall |i: int, j: int| #![trigger result[i], result[j]]
            0 <= i < j < result.len() ==> result[i] != result[j],
{
    // --- Step 1: Build identity permutation [0, 1, ..., n-1] ---
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            nums.len() == k,
            1 <= n <= 100_000,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == i as i32,
        decreases n - k,
    {
        nums.push(k as i32);
        k = k + 1;
    }

    // --- Step 2: Optionally swap two positions ---
    if mutation_kind != 0 && swap_i != swap_j {
        let a = nums[swap_i];
        let b = nums[swap_j];
        nums.set(swap_i, b);
        nums.set(swap_j, a);

        proof {
            // After swap: nums[swap_i] == swap_j, nums[swap_j] == swap_i,
            // other positions unchanged.
            assert(nums[swap_i as int] == swap_j as i32);
            assert(nums[swap_j as int] == swap_i as i32);

            // Range: every element is in [0, n)
            assert forall |i: int| 0 <= i < nums.len()
                implies 0 <= #[trigger] nums[i] < nums.len()
            by {
                if i == swap_i as int {
                    assert(nums[i] == swap_j as i32);
                } else if i == swap_j as int {
                    assert(nums[i] == swap_i as i32);
                } else {
                    assert(nums[i] == i as i32);
                }
            };

            // Uniqueness: all elements are distinct
            assert forall |i: int, j: int| #![trigger nums[i], nums[j]]
                0 <= i < j < nums.len() implies nums[i] != nums[j]
            by {
                if i == swap_i as int && j == swap_j as int {
                    // swap_j != swap_i
                } else if i == swap_i as int && j == swap_j as int {
                    // duplicate arm — unreachable
                } else if i == swap_i as int {
                    // nums[i] = swap_j, nums[j] = j (j != swap_j)
                    assert(nums[i] == swap_j as i32);
                    if j == swap_j as int {
                        // already handled
                    } else {
                        assert(nums[j] == j as i32);
                        // swap_j != j because j != swap_j
                    }
                } else if i == swap_j as int {
                    assert(nums[i] == swap_i as i32);
                    if j == swap_i as int {
                        // nums[j] = swap_j, swap_i != swap_j
                    } else if j == swap_j as int {
                        // i == swap_j == j contradicts i < j
                    } else {
                        assert(nums[j] == j as i32);
                        // swap_i != j because j != swap_i
                    }
                } else if j == swap_i as int {
                    assert(nums[i] == i as i32);
                    assert(nums[j] == swap_j as i32);
                    // i != swap_j because i != swap_j (from outer else)
                } else if j == swap_j as int {
                    assert(nums[i] == i as i32);
                    assert(nums[j] == swap_i as i32);
                    // i != swap_i because i != swap_i (from outer else)
                } else {
                    assert(nums[i] == i as i32);
                    assert(nums[j] == j as i32);
                }
            };
        }
    } else {
        // Identity or swap_i == swap_j (no-op swap)
        proof {
            assert forall |i: int| 0 <= i < nums.len()
                implies 0 <= #[trigger] nums[i] < nums.len()
            by {
                assert(nums[i] == i as i32);
            };
            assert forall |i: int, j: int| #![trigger nums[i], nums[j]]
                0 <= i < j < nums.len() implies nums[i] != nums[j]
            by {
                assert(nums[i] == i as i32);
                assert(nums[j] == j as i32);
            };
        }
    }

    nums
}

} // verus!

// ---------------------------------------------------------------------------
// Runtime: PRNG, main, JSONL output
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::collections::HashSet;
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(775);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<Vec<i32>>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count || !seen.insert(nums.clone()) {
            return;
        }
        let output = Solution::is_ideal_permutation(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // --- Example inputs from description.md ---
    emit(vec![1, 0, 2], &mut seen, &mut out, &mut emitted);
    emit(vec![1, 2, 0], &mut seen, &mut out, &mut emitted);

    // --- Small hand-crafted seeds ---
    // Identity permutations of various small sizes
    for n in [1, 2, 3, 4, 5, 6, 10].iter() {
        let n = *n;
        let perm = generate_test_case(n, 0, 0, 0); // identity
        emit(perm, &mut seen, &mut out, &mut emitted);
    }

    // Adjacent swaps at every position for a small array
    for pos in 0..9 {
        let perm = generate_test_case(10, pos, pos + 1, 1);
        emit(perm, &mut seen, &mut out, &mut emitted);
    }

    // Non-adjacent swaps (should produce global non-local inversions → false)
    for &(si, sj) in &[(0usize, 2), (0, 5), (0, 9), (3, 7), (1, 9), (2, 8)] {
        let perm = generate_test_case(10, si, sj, 1);
        emit(perm, &mut seen, &mut out, &mut emitted);
    }

    // --- Systematic mutations across size classes ---
    let size_classes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100, 500, 1000, 5000, 10000];

    for &n in &size_classes {
        // Identity (no swap)
        let perm = generate_test_case(n, 0, 0, 0);
        emit(perm, &mut seen, &mut out, &mut emitted);

        if n >= 2 {
            // Adjacent swap at beginning
            let perm = generate_test_case(n, 0, 1, 1);
            emit(perm, &mut seen, &mut out, &mut emitted);

            // Adjacent swap at end
            let perm = generate_test_case(n, n - 2, n - 1, 1);
            emit(perm, &mut seen, &mut out, &mut emitted);

            // Non-adjacent swap: first and last
            let perm = generate_test_case(n, 0, n - 1, 1);
            emit(perm, &mut seen, &mut out, &mut emitted);
        }

        if n >= 3 {
            // Swap at middle
            let mid = n / 2;
            let perm = generate_test_case(n, mid, mid + 1, 1);
            emit(perm, &mut seen, &mut out, &mut emitted);

            // Non-adjacent: first and middle
            let perm = generate_test_case(n, 0, mid, 1);
            emit(perm, &mut seen, &mut out, &mut emitted);
        }
    }

    // --- Random test cases to fill up to count ---
    while emitted < count {
        // Pick a size class
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(2, 20),       // small
            2 => rng.gen_range_usize(21, 500),     // medium
            3 => rng.gen_range_usize(501, 5000),   // large
            _ => rng.gen_range_usize(5001, 100_000), // max
        };

        let mutation = rng.gen_range_usize(0, 3) as u8;
        let swap_i = rng.gen_range_usize(0, n - 1);
        let swap_j = if mutation == 0 {
            // No swap — values don't matter but must be < n
            0
        } else if mutation == 1 && n >= 2 {
            // Adjacent swap
            if swap_i + 1 < n { swap_i + 1 } else { swap_i - 1 }
        } else {
            // General swap (may be non-adjacent)
            rng.gen_range_usize(0, n - 1)
        };

        let perm = generate_test_case(n, swap_i, swap_j, mutation);
        emit(perm, &mut seen, &mut out, &mut emitted);
    }
}
