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

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        deltas.len() + 1 <= 10_000,
        -10_000 <= base <= 10_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> -10_000 <= #[trigger] result[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
{
    // Build sorted (non-decreasing) array from cumulative sums of deltas
    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            nums.len() == idx + 1,
            deltas.len() + 1 <= 10_000,
            -10_000 <= base <= 10_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 0i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
            forall|k: int| 0 <= k <= idx as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> -10_000 <= #[trigger] nums[k] <= 10_000,
            forall|k: int, l: int| 0 <= k <= l < nums.len() ==> nums[k] <= nums[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = nums[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(-10_000 <= next <= 10_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int) <= 10_000);
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
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
            assert forall|k: int, l: int| 0 <= k <= l < nums.len() implies nums[k] <= nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    // Apply mutations
    if mutation_kind == 1 {
        // Single element: base
        let mut r: Vec<i32> = Vec::new();
        r.push(base);
        r
    } else if mutation_kind == 2 {
        // Single element: last value of constructed array
        let last_idx = nums.len() - 1;
        let last_val = nums[last_idx];
        let mut r: Vec<i32> = Vec::new();
        r.push(last_val);
        r
    } else if mutation_kind == 3 {
        // Constant array: all elements equal to base, same length
        let n = nums.len();
        let mut flat: Vec<i32> = Vec::new();
        let mut m: usize = 0;
        while m < n
            invariant
                0 <= m <= n,
                flat.len() == m,
                1 <= n <= 10_000,
                -10_000 <= base <= 10_000,
                forall|k: int| 0 <= k < flat.len() ==> #[trigger] flat[k] == base,
            decreases n - m,
        {
            flat.push(base);
            m = m + 1;
        }
        proof {
            assert(flat.len() == n);
            assert forall|i: int| 0 <= i < flat.len()
                implies -10_000 <= #[trigger] flat[i] <= 10_000 by {
                assert(flat[i] == base);
            };
            assert forall|i: int, j: int| 0 <= i <= j < flat.len()
                implies flat[i] <= flat[j] by {
                assert(flat[i] == base);
                assert(flat[j] == base);
            };
        }
        flat
    } else {
        // Identity: return constructed sorted array
        nums
    }
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
        deltas.push(rng.gen_range_i64(0, max_d as i64) as i32);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(977);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let mk_val: u8 = $mk;
                let nums = generate_test_case(&deltas_val, base_val, mk_val);
                let result = Solution::sorted_squares(nums.clone());
                let line = json!({
                    "input": {"nums": nums},
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
    emit!(sorted_to_deltas(&[-4, -1, 0, 3, 10]), -4, 0);
    emit!(sorted_to_deltas(&[-7, -3, 2, 3, 11]), -7, 0);

    // ---- Single element, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![], 0, mk);
        emit!(vec![], -10_000, mk);
        emit!(vec![], 10_000, mk);
        emit!(vec![], 1, mk);
        emit!(vec![], -1, mk);
    }

    // ---- Two elements, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![0], 0, mk);              // [0, 0]
        emit!(vec![1], -1, mk);             // [-1, 0]
        emit!(vec![5], -3, mk);             // [-3, 2]
        emit!(vec![20000], -10_000, mk);    // [-10000, 10000]
    }

    // ---- Small arrays with zero deltas (all same values) ----
    for mk in 0u8..=3 {
        emit!(vec![0, 0, 0, 0], 5, mk);
        emit!(vec![0, 0, 0, 0], -5, mk);
    }

    // ---- Small sorted arrays with mixed deltas ----
    for mk in 0u8..=3 {
        emit!(vec![1, 2, 3, 4], -5, mk);
        emit!(vec![0, 0, 1, 0], 0, mk);
    }

    // ---- All negative values ----
    emit!(sorted_to_deltas(&[-10_000, -9999, -9998, -9997, -9996]), -10_000, 0);

    // ---- All positive values ----
    emit!(sorted_to_deltas(&[9996, 9997, 9998, 9999, 10_000]), 9996, 0);

    // ---- Spanning zero ----
    for mk in [0u8, 1, 2, 3] {
        emit!(vec![1; 100], -50, mk);
    }

    // ---- Near boundaries ----
    emit!(vec![1, 1, 1, 1, 1, 1, 1, 1, 1], 9991, 0);
    emit!(vec![1, 1, 1, 1, 1, 1, 1, 1, 1], -10_000, 0);

    // ---- Random tiny arrays (2-5 elements), all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(2, 5);
        let max_d = 100i32;
        let deltas = random_deltas(&mut rng, n, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total);
        let base = if hi < -10_000 { -10_000i32 } else {
            rng.gen_range_i64(-10_000, hi) as i32
        };
        for mk in 0u8..=3 {
            emit!(deltas.clone(), base, mk);
        }
    }

    // ---- Random medium arrays (10-200 elements), mixed deltas ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(10, 200);
        let max_d = std::cmp::max(1, (20_000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total);
        let base = if hi < -10_000 { -10_000i32 } else {
            rng.gen_range_i64(-10_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3) as u8) % 4;
        emit!(deltas.clone(), base, mk);
        emit!(deltas.clone(), base, 0);
    }

    // ---- Random large arrays (500-5000 elements), small deltas ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(500, 5000);
        let deltas: Vec<i32> = (0..n - 1).map(|_|
            rng.gen_range_i64(0, 1) as i32
        ).collect();
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total);
        let base = if hi < -10_000 { -10_000i32 } else {
            rng.gen_range_i64(-10_000, hi) as i32
        };
        for mk in [0u8, 1, 2, 3] {
            emit!(deltas.clone(), base, mk);
        }
    }

    // ---- Maximum size (10000 elements), delta=1 ----
    {
        let deltas = vec![1i32; 9999];
        let base = -5000i32;
        emit!(deltas.clone(), base, 0);
        emit!(deltas.clone(), base, 1);
        emit!(deltas.clone(), base, 2);
        emit!(deltas.clone(), base, 3);
    }

    // ---- Maximum size, all same value (delta=0) ----
    {
        let deltas = vec![0i32; 9999];
        emit!(deltas.clone(), 0, 0);
        emit!(deltas.clone(), 0, 3);
        emit!(deltas.clone(), -10_000, 0);
        emit!(deltas.clone(), 10_000, 0);
    }

    // ---- Fill remaining with random sizes ----
    while count < goal {
        let n = rng.gen_range_usize(1, 500);
        let max_d = std::cmp::max(1, (20_000 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total);
        let base = if hi < -10_000 { -10_000i32 } else {
            rng.gen_range_i64(-10_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3) as u8) % 4;
        emit!(deltas, base, mk);
    }
}
