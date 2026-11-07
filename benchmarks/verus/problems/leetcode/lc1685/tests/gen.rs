use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when all deltas >= 0.
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
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= deltas.len() + 1 <= 100_000,
        1 <= base <= 10_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
    ensures
        2 <= result@.len() <= 100_000,
        forall|i: int| 0 <= i < result@.len() ==> 1 <= #[trigger] result@[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < result@.len() ==> result@[i] <= result@[j],
{
    if mutation_kind == 1 {
        // Constant array: all elements equal to base
        let n = deltas.len() + 1;
        let mut nums: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == deltas.len() + 1,
                nums.len() == k,
                1 <= base <= 10_000,
                2 <= n <= 100_000,
                forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] nums[idx] == base,
            decreases n - k,
        {
            nums.push(base);
            k = k + 1;
        }
        proof {
            assert(nums.len() == n);
            assert forall|i: int| 0 <= i < nums@.len() implies 1 <= #[trigger] nums@[i] <= 10_000 by {
                assert(nums@[i] == base);
            };
            assert forall|i: int, j: int| 0 <= i <= j < nums@.len() implies nums@[i] <= nums@[j] by {
                assert(nums@[i] == base);
                assert(nums@[j] == base);
            };
        }
        nums
    } else {
        // Standard construction: build sorted array from base + cumulative deltas
        let mut nums: Vec<i32> = Vec::new();
        nums.push(base);

        let mut i: usize = 0;
        while i < deltas.len()
            invariant
                0 <= i <= deltas.len(),
                nums.len() == i + 1,
                deltas.len() + 1 <= 100_000,
                1 <= base <= 10_000,
                forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 0i32,
                base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
                forall|k: int| 0 <= k <= i as int ==>
                    #[trigger] nums[k] as int == base as int + sum_deltas(deltas@, k),
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
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

                assert(1 <= next <= 10_000) by {
                    assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                    assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                        <= base as int + sum_deltas(deltas@, deltas.len() as int));
                    assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 10_000);
                    lemma_sum_deltas_nonneg(deltas@, (i + 1) as int);
                    assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                    assert(next as int >= base as int);
                    assert(next >= 1);
                };

                assert forall|k: int| 0 <= k < old_len as int implies nums[k] <= next by {
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

fn capped_deltas(rng: &mut Rng, count: usize, base: i32) -> Vec<i32> {
    let budget = 10_000 - base as i64;
    let mut deltas = Vec::new();
    let mut used: i64 = 0;
    for _ in 0..count {
        let remaining = budget - used;
        if remaining <= 0 {
            deltas.push(0);
        } else {
            let d = rng.gen_range_i64(0, remaining.min(100)) as i32;
            deltas.push(d);
            used += d as i64;
        }
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1685);
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
                let result = Solution::get_sum_absolute_differences(nums.clone());
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
    emit!(sorted_to_deltas(&[2, 3, 5]), 2, 0);
    emit!(sorted_to_deltas(&[1, 4, 6, 8, 10]), 1, 0);

    // ---- Constant arrays (mutation_kind = 1) ----
    emit!(vec![0], 1, 1);
    emit!(vec![0; 4], 5, 1);
    emit!(vec![0; 9], 10000, 1);

    // ---- Small arrays with all mutations ----
    for mk in 0u8..=1 {
        emit!(vec![1], 1, mk);
        emit!(vec![0], 5000, mk);
        emit!(vec![1, 2, 3], 1, mk);
        emit!(vec![0, 0, 0], 1, mk);
    }

    // ---- Boundary values ----
    emit!(vec![0], 10000, 0);
    emit!(sorted_to_deltas(&[1, 10000]), 1, 0);
    emit!(vec![1, 1, 1, 1, 1], 9995, 0);
    emit!(vec![1, 1, 1, 1, 1], 1, 0);

    // ---- Two elements, varied ----
    emit!(vec![9999], 1, 0);
    emit!(vec![4999], 5000, 0);

    // ---- Medium arrays with varied structure ----
    emit!(sorted_to_deltas(&[1, 1, 2, 3, 5, 8, 13, 21]), 1, 0);
    emit!(sorted_to_deltas(&[100, 200, 300, 400, 500]), 100, 0);

    // ---- Random test cases with size classes ----
    while count < goal {
        let mk = (rng.next_u64() % 2) as u8;

        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };

        let base = rng.gen_range_i64(1, 5000) as i32;
        let deltas_val = capped_deltas(&mut rng, n - 1, base);
        emit!(deltas_val, base, mk);
    }

    eprintln!("Generated {} test cases", count);
}
