use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when every delta >= 0.
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

/// sum_deltas is non-negative when every delta >= 0.
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
    n: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        0 <= deltas.len() <= 999,
        1 <= base <= 10000,
        1 <= n <= 2147483647,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 10000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= 2147483647,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
{
    // Mutation 3: single-element array [base]
    if mutation_kind == 3 {
        let mut single: Vec<i32> = Vec::new();
        single.push(base);
        return (single, n);
    }

    // Mutation 4: uniform array of all base values
    if mutation_kind == 4 {
        let target_len: usize = (deltas.len() + 1) as usize;
        let mut uniform: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < target_len
            invariant
                0 <= k <= target_len,
                uniform.len() == k as int,
                1 <= target_len <= 1000,
                1 <= base <= 10000,
                forall|i: int| 0 <= i < uniform.len() ==> #[trigger] uniform[i] == base,
            decreases target_len - k,
        {
            uniform.push(base);
            k = k + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < uniform.len()
                implies 1 <= #[trigger] uniform[i] <= 10000
            by {
                assert(uniform[i] == base);
            };
            assert forall|i: int, j: int| 0 <= i < j < uniform.len()
                implies uniform[i] <= uniform[j]
            by {
                assert(uniform[i] == base);
                assert(uniform[j] == base);
            };
        }
        return (uniform, n);
    }

    // Default path: build sorted array from deltas
    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            nums.len() == (idx + 1) as int,
            0 <= deltas.len() <= 999,
            1 <= base <= 10000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 0i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 10000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= idx as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10000,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] <= nums[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
            lemma_sum_deltas_nonneg(deltas@, (idx + 1) as int);
        }

        let next = nums[idx] + deltas[idx];

        proof {
            assert(nums[idx as int] as int == base as int + sum_deltas(deltas@, idx as int));
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));

            assert(1 <= next <= 10000) by {
                lemma_sum_deltas_nonneg(deltas@, (idx + 1) as int);
                lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
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
            assert forall|k: int, l: int| 0 <= k < l < nums.len()
                implies nums[k] <= nums[l]
            by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    // Apply n mutations
    let mutated_n: i32 = if mutation_kind == 1 {
        1i32                                          // minimum n
    } else if mutation_kind == 2 {
        2147483647i32                                 // maximum n
    } else {
        n                                             // identity
    };

    (nums, mutated_n)
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

struct Solution;
include!("../code.rs");

fn random_deltas(rng: &mut Rng, count: usize, max_delta: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..count {
        deltas.push(rng.gen_range_i64(0, max_delta as i64) as i32);
    }
    deltas
}

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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(330);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $n:expr, $mk:expr) => {{
            let (nums, n_val) = generate_test_case(&$deltas, $base, $n, $mk);
            let key = format!("{:?}:{}", nums, n_val);
            if seen.insert(key) {
                let nums_clone = nums.clone();
                let result = Solution::min_patches(nums, n_val);
                writeln!(out, "{}", json!({
                    "input": {"nums": nums_clone, "n": n_val},
                    "output": result
                })).unwrap();
                total += 1;
            }
        }};
    }

    // ---- Examples from description.md ----
    emit!(sorted_to_deltas(&[1, 3]), 1, 6, 0u8);
    emit!(sorted_to_deltas(&[1, 5, 10]), 1, 20, 0u8);
    emit!(sorted_to_deltas(&[1, 2, 2]), 1, 5, 0u8);

    // Examples with all mutations
    for mk in 0u8..=4 {
        emit!(sorted_to_deltas(&[1, 3]), 1, 6, mk);
        emit!(sorted_to_deltas(&[1, 5, 10]), 1, 20, mk);
        emit!(sorted_to_deltas(&[1, 2, 2]), 1, 5, mk);
    }

    // ---- Boundary cases ----
    emit!(vec![], 1, 1, 0u8);                  // single element [1], min n
    emit!(vec![], 1, 2147483647, 0u8);          // single element [1], max n
    emit!(vec![], 10000, 1, 0u8);               // single element [10000], min n
    emit!(vec![], 10000, 2147483647, 0u8);       // single element [10000], max n
    emit!(vec![0; 999], 1, 100, 0u8);           // max length, all 1s
    emit!(vec![0; 999], 5000, 100, 0u8);        // max length, all 5000s

    // ---- Various n boundary values ----
    for &n_val in &[1i32, 2, 10, 100, 1000, 10000, 100000, 1000000, 2147483647] {
        emit!(sorted_to_deltas(&[1, 2, 3]), 1, n_val, 0u8);
    }

    // ---- Consecutive arrays [base, base+1, base+2, ...] ----
    for &len in &[2usize, 5, 10, 50, 100, 500, 1000] {
        let num_deltas = len - 1;
        if num_deltas <= 999 {
            let deltas: Vec<i32> = vec![1i32; num_deltas];
            let total_sum = num_deltas as i64;
            let max_base = (10000i64 - total_sum).min(10000);
            if max_base >= 1 {
                let base = std::cmp::max(1, std::cmp::min(max_base as i32, 1));
                let n_val = rng.gen_range_i64(1, 2147483647) as i32;
                for mk in 0u8..=4 {
                    if total < count {
                        emit!(deltas.clone(), base, n_val, mk);
                    }
                }
            }
        }
    }

    // ---- Random tiny arrays (1-5 elements), all mutations ----
    for _ in 0..5 {
        let len = rng.gen_range_usize(1, 5);
        let num_deltas = if len > 0 { len - 1 } else { 0 };
        let budget = 10000i64 - 1;
        let max_d = if num_deltas > 0 {
            std::cmp::min((budget / num_deltas as i64) as i32, 100)
        } else {
            0
        };
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::max(max_d, 0));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = (10000i64 - total_sum).min(10000);
        if max_base >= 1 {
            let base = rng.gen_range_i64(1, max_base) as i32;
            let n_val = rng.gen_range_i64(1, 2147483647) as i32;
            for mk in 0u8..=4 {
                if total < count {
                    emit!(deltas.clone(), base, n_val, mk);
                }
            }
        }
    }

    // ---- Random medium arrays (10-100 elements) ----
    for _ in 0..8 {
        let len = rng.gen_range_usize(10, 100);
        let num_deltas = len - 1;
        let budget = 10000i64 - 1;
        let max_d = std::cmp::min((budget / std::cmp::max(num_deltas as i64, 1)) as i32, 50);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::max(max_d, 0));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = (10000i64 - total_sum).min(10000);
        if max_base >= 1 {
            let base = rng.gen_range_i64(1, max_base) as i32;
            let n_val = rng.gen_range_i64(1, 2147483647) as i32;
            let mk = (rng.gen_range_i64(0, 4) as u8) % 5;
            if total < count {
                emit!(deltas, base, n_val, mk);
            }
        }
    }

    // ---- Random large arrays (100-500 elements) ----
    for _ in 0..5 {
        let len = rng.gen_range_usize(100, 500);
        let num_deltas = len - 1;
        let budget = 10000i64 - 1;
        let max_d = std::cmp::min((budget / std::cmp::max(num_deltas as i64, 1)) as i32, 20);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::max(max_d, 0));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = (10000i64 - total_sum).min(10000);
        if max_base >= 1 {
            let base = rng.gen_range_i64(1, max_base) as i32;
            let n_val = rng.gen_range_i64(1, 2147483647) as i32;
            if total < count {
                emit!(deltas, base, n_val, 0u8);
            }
        }
    }

    // ---- Maximum length (1000 elements), all equal ----
    emit!(vec![0i32; 999], 1, 2147483647, 0u8);
    emit!(vec![0i32; 999], 10000, 1, 0u8);
    emit!(vec![0i32; 999], 5, 1000000, 4u8);  // uniform mutation

    // ---- Fill remaining with random sizes and mutations ----
    while total < count {
        let len = rng.gen_range_usize(1, 200);
        let num_deltas = if len > 0 { len - 1 } else { 0 };
        let budget = 10000i64 - 1;
        let max_d = if num_deltas > 0 {
            std::cmp::min((budget / num_deltas as i64) as i32, 30)
        } else {
            0
        };
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::max(max_d, 0));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = (10000i64 - total_sum).min(10000);
        if max_base >= 1 {
            let base = rng.gen_range_i64(1, max_base) as i32;
            let n_val = rng.gen_range_i64(1, 2147483647) as i32;
            let mk = (rng.gen_range_i64(0, 4) as u8) % 5;
            emit!(deltas, base, n_val, mk);
        }
    }
}
