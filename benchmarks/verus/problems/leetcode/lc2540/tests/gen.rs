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

/// Non-decreasing: for a <= b, sum at a <= sum at b when deltas >= 0.
proof fn lemma_sum_deltas_nondecreasing(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    lemma_sum_deltas_mono(deltas, a, b);
}

/// Build a non-decreasing array from a base value and non-negative deltas.
/// nums[0] = base, nums[k+1] = nums[k] + deltas[k].
pub fn build_sorted_array(
    deltas: &Vec<i32>,
    base: i32,
) -> (result: Vec<i32>)
    requires
        deltas.len() + 1 <= 100_000,
        1 <= base <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        result.len() == deltas.len() + 1,
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            nums.len() == idx + 1,
            deltas.len() + 1 <= 100_000,
            1 <= base <= 1_000_000_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 0i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= idx as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] <= nums[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = nums[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(1 <= next <= 1_000_000_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int) <= 1_000_000_000);
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int) >= base as int);
                assert(base as int >= 1);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] <= next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_mono(deltas@, k, (idx + 1) as int);
            };
        }

        nums.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] <= nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    nums
}

pub fn generate_test_case(
    deltas1: &Vec<i32>,
    base1: i32,
    deltas2: &Vec<i32>,
    base2: i32,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        deltas1.len() + 1 <= 100_000,
        deltas2.len() + 1 <= 100_000,
        1 <= base1 <= 1_000_000_000,
        1 <= base2 <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas1.len() ==> 0 <= #[trigger] deltas1[i],
        forall|i: int| 0 <= i < deltas2.len() ==> 0 <= #[trigger] deltas2[i],
        base1 as int + sum_deltas(deltas1@, deltas1.len() as int) <= 1_000_000_000,
        base2 as int + sum_deltas(deltas2@, deltas2.len() as int) <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] <= result.1[j],
{
    let nums1 = build_sorted_array(deltas1, base1);
    let nums2 = build_sorted_array(deltas2, base2);
    (nums1, nums2)
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn sorted_to_deltas(vals: &[i32]) -> Vec<i32> {
    let mut deltas = Vec::new();
    for i in 1..vals.len() {
        deltas.push(vals[i] - vals[i - 1]);
    }
    deltas
}

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range(0, max_d as i64) as i32);
    }
    deltas
}

fn delta_sum(deltas: &[i32]) -> i64 {
    deltas.iter().map(|d| *d as i64).sum()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2540);
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($d1:expr, $b1:expr, $d2:expr, $b2:expr) => {
            if count < count_goal {
                let d1_val: Vec<i32> = $d1;
                let b1_val: i32 = $b1;
                let d2_val: Vec<i32> = $d2;
                let b2_val: i32 = $b2;
                let (nums1, nums2) = generate_test_case(&d1_val, b1_val, &d2_val, b2_val);
                let result = Solution::get_common(nums1.clone(), nums2.clone());
                let line = json!({
                    "input": {"nums1": nums1, "nums2": nums2},
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
    // Example 1: nums1 = [1,2,3], nums2 = [2,4] => 2
    emit!(sorted_to_deltas(&[1, 2, 3]), 1, sorted_to_deltas(&[2, 4]), 2);
    // Example 2: nums1 = [1,2,3,6], nums2 = [2,3,4,5] => 2
    emit!(sorted_to_deltas(&[1, 2, 3, 6]), 1, sorted_to_deltas(&[2, 3, 4, 5]), 2);

    // ---- Single element arrays ----
    // Same element => common
    emit!(vec![], 5, vec![], 5);
    // Different elements => -1
    emit!(vec![], 1, vec![], 2);
    // Boundary values
    emit!(vec![], 1, vec![], 1);
    emit!(vec![], 1_000_000_000, vec![], 1_000_000_000);
    emit!(vec![], 1, vec![], 1_000_000_000);

    // ---- No overlap (disjoint ranges) ----
    emit!(sorted_to_deltas(&[1, 2, 3]), 1, sorted_to_deltas(&[4, 5, 6]), 4);
    emit!(sorted_to_deltas(&[10, 20, 30]), 10, sorted_to_deltas(&[1, 2, 3]), 1);

    // ---- Full overlap (identical arrays) ----
    emit!(sorted_to_deltas(&[1, 2, 3, 4, 5]), 1, sorted_to_deltas(&[1, 2, 3, 4, 5]), 1);

    // ---- Partial overlap ----
    emit!(sorted_to_deltas(&[1, 3, 5, 7]), 1, sorted_to_deltas(&[2, 4, 5, 8]), 2);
    emit!(sorted_to_deltas(&[1, 2, 3]), 1, sorted_to_deltas(&[3, 4, 5]), 3);

    // ---- Duplicates in arrays (non-decreasing, not strictly increasing) ----
    emit!(sorted_to_deltas(&[1, 1, 2, 3]), 1, sorted_to_deltas(&[1, 1, 3, 3]), 1);
    emit!(sorted_to_deltas(&[2, 2, 2]), 2, sorted_to_deltas(&[2, 2, 2]), 2);
    emit!(sorted_to_deltas(&[1, 1, 1, 1]), 1, sorted_to_deltas(&[2, 2, 2, 2]), 2);

    // ---- One array much longer ----
    emit!(vec![1; 99], 1, vec![], 50);
    emit!(vec![], 5, vec![1; 99], 1);

    // ---- Arrays with all same elements ----
    emit!(vec![0; 49], 42, vec![0; 49], 42);
    emit!(vec![0; 49], 42, vec![0; 49], 43);

    // ---- Boundary: minimum common at the end ----
    emit!(sorted_to_deltas(&[1, 2, 3, 10]), 1, sorted_to_deltas(&[4, 5, 10]), 4);

    // ---- Random tiny arrays (1-5 elements), overlapping ranges ----
    for _ in 0..8 {
        let n1 = rng.gen_range(1, 5) as usize;
        let n2 = rng.gen_range(1, 5) as usize;
        let base = rng.gen_range(1, 100) as i32;
        let d1 = random_deltas(&mut rng, n1, 10);
        let d2 = random_deltas(&mut rng, n2, 10);
        let s1 = delta_sum(&d1);
        let s2 = delta_sum(&d2);
        if base as i64 + s1 <= 1_000_000_000 && base as i64 + s2 <= 1_000_000_000 {
            emit!(d1, base, d2, base);
        }
    }

    // ---- Random small arrays (5-50 elements), varied bases ----
    for _ in 0..10 {
        let n1 = rng.gen_range(5, 50) as usize;
        let n2 = rng.gen_range(5, 50) as usize;
        let d1 = random_deltas(&mut rng, n1, 20);
        let d2 = random_deltas(&mut rng, n2, 20);
        let s1 = delta_sum(&d1);
        let s2 = delta_sum(&d2);
        let b1 = rng.gen_range(1, std::cmp::max(1, 1_000_000_000i64 - s1)) as i32;
        let b2 = rng.gen_range(1, std::cmp::max(1, 1_000_000_000i64 - s2)) as i32;
        emit!(d1, b1, d2, b2);
    }

    // ---- Random medium arrays (50-500 elements), overlapping ranges for common ----
    for _ in 0..10 {
        let n1 = rng.gen_range(50, 500) as usize;
        let n2 = rng.gen_range(50, 500) as usize;
        let d1 = random_deltas(&mut rng, n1, 5);
        let d2 = random_deltas(&mut rng, n2, 5);
        let s1 = delta_sum(&d1);
        let s2 = delta_sum(&d2);
        let base = rng.gen_range(1, std::cmp::max(1, 1_000_000_000i64 - std::cmp::max(s1, s2))) as i32;
        emit!(d1, base, d2, base);
    }

    // ---- Random large arrays (500-5000 elements), delta=0 or 1 ----
    for _ in 0..5 {
        let n1 = rng.gen_range(500, 5000) as usize;
        let n2 = rng.gen_range(500, 5000) as usize;
        let d1 = random_deltas(&mut rng, n1, 1);
        let d2 = random_deltas(&mut rng, n2, 1);
        let s1 = delta_sum(&d1);
        let s2 = delta_sum(&d2);
        let base = rng.gen_range(1, std::cmp::max(1, 1_000_000_000i64 - std::cmp::max(s1, s2))) as i32;
        emit!(d1, base, d2, base);
    }

    // ---- Disjoint large arrays (no common) ----
    for _ in 0..3 {
        let n1 = rng.gen_range(100, 1000) as usize;
        let n2 = rng.gen_range(100, 1000) as usize;
        let d1 = random_deltas(&mut rng, n1, 3);
        let d2 = random_deltas(&mut rng, n2, 3);
        let s1 = delta_sum(&d1);
        // nums1 in [1, 1+s1], nums2 starts after
        let b2_start = std::cmp::min(1 + s1 + 1, 999_999_000);
        let s2 = delta_sum(&d2);
        if b2_start + s2 <= 1_000_000_000 {
            emit!(d1, 1, d2, b2_start as i32);
        }
    }

    // ---- Large values near boundary ----
    emit!(sorted_to_deltas(&[999_999_990, 999_999_995, 1_000_000_000]), 999_999_990,
          sorted_to_deltas(&[999_999_995, 999_999_998, 1_000_000_000]), 999_999_995);

    // ---- Small values near lower boundary ----
    emit!(sorted_to_deltas(&[1, 1, 1, 2]), 1, sorted_to_deltas(&[1, 2, 2, 3]), 1);

    // ---- Fill remaining with random sizes and random mutations ----
    while count < count_goal {
        let size_class = rng.gen_range(0, 4);
        let (n1, n2, max_d) = match size_class {
            0 => (rng.gen_range(1, 5) as usize, rng.gen_range(1, 5) as usize, 100),
            1 => (rng.gen_range(5, 50) as usize, rng.gen_range(5, 50) as usize, 50),
            2 => (rng.gen_range(50, 500) as usize, rng.gen_range(50, 500) as usize, 10),
            _ => (rng.gen_range(500, 2000) as usize, rng.gen_range(500, 2000) as usize, 2),
        };
        let d1 = random_deltas(&mut rng, n1, max_d);
        let d2 = random_deltas(&mut rng, n2, max_d);
        let s1 = delta_sum(&d1);
        let s2 = delta_sum(&d2);
        let max_s = std::cmp::max(s1, s2);
        let hi = std::cmp::max(1, 1_000_000_000i64 - max_s);
        let base = rng.gen_range(1, hi) as i32;
        emit!(d1, base, d2, base);
    }
}
