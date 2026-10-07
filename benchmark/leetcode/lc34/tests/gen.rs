use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 0.
proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// sum_deltas is non-negative when all deltas >= 0.
proof fn lemma_sum_deltas_nonneg(deltas: Seq<i32>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_deltas_nonneg(deltas, end - 1);
    }
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        deltas.len() <= 99_999,
        -1_000_000_000 <= base <= 1_000_000_000,
        -1_000_000_000 <= target <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        0 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> -1_000_000_000 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i <= j < result.0.len() ==> result.0[i] <= result.0[j],
        -1_000_000_000 <= result.1 <= 1_000_000_000,
{
    // mutation_kind 7: empty array
    if mutation_kind == 7 {
        let empty: Vec<i32> = Vec::new();
        return (empty, target);
    }

    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            nums.len() == i + 1,
            deltas.len() <= 99_999,
            -1_000_000_000 <= base <= 1_000_000_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 0i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= i as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k <= l < nums.len() ==> nums[k] <= nums[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = nums[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(-1_000_000_000 <= next <= 1_000_000_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 1_000_000_000);
                lemma_sum_deltas_nonneg(deltas@, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) >= base as int);
                assert(base as int >= -1_000_000_000);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] <= next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_mono(deltas@, k, (i + 1) as int);
            };
        }

        nums.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k <= l < nums.len() implies nums[k] <= nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    // Compute mutated target
    let mutated_target: i32 =
        if mutation_kind == 1 {
            nums[0]                                       // target = first element
        } else if mutation_kind == 2 {
            let last = nums.len() - 1;
            nums[last]                                    // target = last element
        } else if mutation_kind == 3 {
            let mid = nums.len() / 2;
            nums[mid]                                     // target = middle element
        } else if mutation_kind == 4 && nums[0] > -1_000_000_000 {
            (nums[0] - 1) as i32                          // target below min (not found)
        } else if mutation_kind == 5 {
            let last = nums.len() - 1;
            if nums[last] < 1_000_000_000 {
                (nums[last] + 1) as i32                   // target above max (not found)
            } else {
                target
            }
        } else if mutation_kind == 6 && nums.len() >= 2 {
            if nums[1] - nums[0] > 1 {
                (nums[0] + 1) as i32                      // target in gap (not found)
            } else {
                target
            }
        } else {
            target                                        // use given target
        };

    (nums, mutated_target)
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

/// Build a vector of n random non-negative deltas, each in [0, max_d].
fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n {
        deltas.push(rng.gen_range_i64(0, max_d as i64) as i32);
    }
    deltas
}

/// Build deltas that reproduce a given sorted (non-decreasing) slice.
fn sorted_to_deltas(vals: &[i32]) -> Vec<i32> {
    let mut deltas = Vec::new();
    for i in 1..vals.len() {
        deltas.push(vals[i] - vals[i - 1]);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(34);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $target:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let target_val: i32 = $target;
                let mk_val: u8 = $mk;
                let (nums_out, target_out) = generate_test_case(
                    &deltas_val, base_val, target_val, mk_val,
                );
                let result = Solution::search_range(nums_out.clone(), target_out);
                let line = json!({
                    "input": {"nums": nums_out, "target": target_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: nums = [5,7,7,8,8,10], target = 8 → [3,4]
    emit!(sorted_to_deltas(&[5, 7, 7, 8, 8, 10]), 5, 8, 0);
    // Example 2: nums = [5,7,7,8,8,10], target = 6 → [-1,-1]
    emit!(sorted_to_deltas(&[5, 7, 7, 8, 8, 10]), 5, 6, 0);
    // Example 3: nums = [], target = 0 → [-1,-1]
    emit!(vec![], 0, 0, 7);

    // ---- Empty array with various targets ----
    emit!(vec![], -1_000_000_000, -1_000_000_000, 7);
    emit!(vec![], 1_000_000_000, 1_000_000_000, 7);

    // ---- Single element with all applicable mutations ----
    for mk in 0u8..=7 {
        emit!(vec![], 0, 5, mk);
        emit!(vec![], -1_000_000_000, 0, mk);
        emit!(vec![], 1_000_000_000, 0, mk);
        emit!(vec![], 42, 42, mk);
    }

    // ---- Two elements, all mutations ----
    for mk in 0u8..=7 {
        emit!(vec![0], 5, 5, mk);        // [5, 5] — duplicates
        emit!(vec![3], 0, 3, mk);        // [0, 3] — with gap
        emit!(vec![0], -10, -10, mk);    // [-10, -10]
    }

    // ---- Small arrays with duplicates (key for this problem) ----
    for mk in 0u8..=6 {
        emit!(vec![0, 0, 0, 0], 8, 8, mk);             // [8,8,8,8,8] all same
        emit!(vec![0, 1, 0, 0, 1], 1, 1, mk);           // [1,1,2,2,2,3]
        emit!(vec![2, 0, 0, 2, 0], 1, 3, mk);           // [1,3,3,3,5,5]
    }

    // ---- Arrays with runs of duplicates ----
    emit!(sorted_to_deltas(&[1, 1, 1, 2, 2, 2, 3, 3, 3]), 1, 2, 0);
    emit!(sorted_to_deltas(&[1, 1, 1, 2, 2, 2, 3, 3, 3]), 1, 2, 1);
    emit!(sorted_to_deltas(&[1, 1, 1, 2, 2, 2, 3, 3, 3]), 1, 2, 2);
    emit!(sorted_to_deltas(&[1, 1, 1, 2, 2, 2, 3, 3, 3]), 1, 4, 0);  // target not in array

    // ---- Near boundaries, varied mutations ----
    emit!(vec![0; 9], 999_999_990, 999_999_995, 0);
    emit!(vec![0; 9], 999_999_990, 999_999_995, 1);
    emit!(vec![0; 9], 999_999_990, 999_999_995, 2);
    emit!(vec![1; 9], -1_000_000_000, 0, 0);
    emit!(vec![1; 9], -1_000_000_000, 0, 2);

    // ---- Consecutive spanning zero, varied mutations ----
    for mk in [0u8, 1, 2, 3, 4, 5] {
        emit!(vec![1; 100], -50, 0, mk);
    }

    // ---- Random tiny arrays (2-5 elements), mixed deltas with duplicates ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(2, 5);
        let deltas = random_deltas(&mut rng, n - 1, 2);  // deltas in [0,2] for duplicates
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi_bound = std::cmp::min(1_000_000_000i64, 1_000_000_000 - total);
        let base = rng.gen_range_i64(-1_000_000_000, hi_bound) as i32;
        let t = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        for mk in 0u8..=7 {
            emit!(deltas.clone(), base, t, mk);
        }
    }

    // ---- Random medium arrays (10-200 elements), mixed deltas ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(10, 200);
        let max_d = std::cmp::max(1, (2_000_000_000i64 / n as i64) as i32);
        let deltas = random_deltas(&mut rng, n - 1, std::cmp::min(max_d, 100));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi_bound = std::cmp::min(1_000_000_000i64, 1_000_000_000 - total);
        let base = if hi_bound < -1_000_000_000 {
            -1_000_000_000i32
        } else {
            rng.gen_range_i64(-1_000_000_000, hi_bound) as i32
        };
        let t = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let mk = (rng.gen_range_usize(0, 7)) as u8;
        emit!(deltas.clone(), base, t, mk);
        emit!(deltas.clone(), base, t, 0);
    }

    // ---- All-same arrays (delta=0), various sizes ----
    for val in [-1_000_000_000i32, -1, 0, 1, 1_000_000_000] {
        let n = 50;
        emit!(vec![0; n - 1], val, val, 0);       // target matches all
        emit!(vec![0; n - 1], val, val + 1, 0);   // target doesn't match (when not overflow)
    }

    // ---- Large arrays (500-5000 elements), delta=0 (all same value) ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(500, 5000);
        let val = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let deltas = vec![0i32; n - 1];
        emit!(deltas.clone(), val, val, 0);        // found: entire array
        emit!(deltas.clone(), val, val, 1);
        emit!(deltas.clone(), val, val, 2);
    }

    // ---- Large arrays with delta=1 (strictly increasing) ----
    for _ in 0..2 {
        let n = rng.gen_range_usize(500, 5000);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let hi_bound = std::cmp::min(1_000_000_000i64, 1_000_000_000 - total);
        let base = if hi_bound < -1_000_000_000 {
            -1_000_000_000i32
        } else {
            rng.gen_range_i64(-1_000_000_000, hi_bound) as i32
        };
        let t = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        for mk in [0u8, 1, 2, 3] {
            emit!(deltas.clone(), base, t, mk);
        }
    }

    // ---- Maximum size (100000 elements), delta=0 ----
    {
        let deltas = vec![0i32; 99_999];
        emit!(deltas.clone(), 42, 42, 0);
        emit!(deltas.clone(), 42, 42, 1);
        emit!(deltas.clone(), 42, 42, 2);
        emit!(deltas.clone(), 42, 99, 0);  // not found
    }

    // ---- Large deltas (spread out), small arrays for gap mutation ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(2, 10);
        let max_d = std::cmp::max(2, (2_000_000_000i64 / n as i64) as i32);
        let deltas = random_deltas(&mut rng, n - 1, std::cmp::min(max_d, 1000));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi_bound = std::cmp::min(1_000_000_000i64, 1_000_000_000 - total);
        let base = if hi_bound < -1_000_000_000 {
            -1_000_000_000i32
        } else {
            rng.gen_range_i64(-1_000_000_000, hi_bound) as i32
        };
        let t = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        emit!(deltas.clone(), base, t, 6);
        emit!(deltas.clone(), base, t, 0);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let n = rng.gen_range_usize(1, 500);
        let max_d = std::cmp::max(1, (2_000_000_000i64 / std::cmp::max(n, 1) as i64) as i32);
        let deltas = random_deltas(&mut rng, n - 1, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi_bound = std::cmp::min(1_000_000_000i64, 1_000_000_000 - total);
        let base = if hi_bound < -1_000_000_000 {
            -1_000_000_000i32
        } else {
            rng.gen_range_i64(-1_000_000_000, hi_bound) as i32
        };
        let target = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;
        emit!(deltas, base, target, mk);
    }

    eprintln!("Generated {} test cases", count);
}
