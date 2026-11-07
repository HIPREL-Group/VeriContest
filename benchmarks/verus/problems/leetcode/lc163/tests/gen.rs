use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 1.
proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// Two partial sums differ by at least (b - a) when every delta >= 1.
proof fn lemma_sum_deltas_strict(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    lower: i32,
    upper: i32,
    base: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        deltas.len() <= 99,
        -1000000000 <= lower <= 1000000000,
        -1000000000 <= upper <= 1000000000,
        lower <= upper,
        lower <= base <= upper,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= upper as int,
    ensures
        0 <= result.0.len() <= 100,
        result.1 <= result.2,
        -1000000000 <= result.1 <= 1000000000,
        -1000000000 <= result.2 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> result.1 <= #[trigger] result.0[i] <= result.2,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] < result.0[j],
{
    if mutation_kind == 1 {
        // Empty array — all of [lower, upper] is missing
        let empty: Vec<i32> = Vec::new();
        (empty, lower, upper)
    } else if mutation_kind == 2 {
        // Single element at lower
        let mut single: Vec<i32> = Vec::new();
        single.push(lower);
        (single, lower, upper)
    } else if mutation_kind == 3 {
        // Single element at upper
        let mut single: Vec<i32> = Vec::new();
        single.push(upper);
        (single, lower, upper)
    } else if mutation_kind == 4 {
        // Single element at base (somewhere in [lower, upper])
        let mut single: Vec<i32> = Vec::new();
        single.push(base);
        (single, lower, upper)
    } else {
        // Build sorted array from base using deltas
        let mut nums: Vec<i32> = Vec::new();
        nums.push(base);

        let mut k: usize = 0;
        while k < deltas.len()
            invariant
                0 <= k <= deltas.len(),
                nums.len() == k + 1,
                deltas.len() <= 99,
                -1000000000 <= lower <= 1000000000,
                -1000000000 <= upper <= 1000000000,
                lower <= base <= upper,
                lower <= upper,
                forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
                base as int + sum_deltas(deltas@, deltas.len() as int) <= upper as int,
                forall|j: int| 0 <= j <= k as int ==>
                    #[trigger] nums[j] == (base as int + sum_deltas(deltas@, j)) as i32,
                forall|j: int| 0 <= j <= k as int ==>
                    nums[j] as int == base as int + sum_deltas(deltas@, j),
                forall|j: int| 0 <= j < nums.len() ==> lower <= #[trigger] nums[j] <= upper,
                forall|j: int, l: int| 0 <= j < l < nums.len() ==> nums[j] < nums[l],
            decreases deltas.len() - k,
        {
            let ghost old_len = nums.len();

            proof {
                lemma_sum_deltas_mono(deltas@, (k + 1) as int, deltas.len() as int);
            }

            let next = nums[k] + deltas[k];

            proof {
                assert(next as int == base as int + sum_deltas(deltas@, (k + 1) as int));
                assert(next <= upper) by {
                    assert(next as int == base as int + sum_deltas(deltas@, (k + 1) as int));
                    assert(base as int + sum_deltas(deltas@, (k + 1) as int)
                        <= base as int + sum_deltas(deltas@, deltas.len() as int));
                    assert(base as int + sum_deltas(deltas@, (k + 1) as int) <= upper as int);
                };
                assert(lower <= next) by {
                    lemma_sum_deltas_mono(deltas@, 0, (k + 1) as int);
                    assert(sum_deltas(deltas@, (k + 1) as int) >= 0);
                    assert(next as int == base as int + sum_deltas(deltas@, (k + 1) as int));
                    assert(next as int >= base as int >= lower as int);
                };

                assert forall|j: int| 0 <= j < nums.len() implies nums[j] < next by {
                    assert(nums[j] as int == base as int + sum_deltas(deltas@, j));
                    assert(next as int == base as int + sum_deltas(deltas@, (k + 1) as int));
                    lemma_sum_deltas_strict(deltas@, j, (k + 1) as int);
                };
            }

            nums.push(next);
            k = k + 1;

            proof {
                assert forall|j: int, l: int| 0 <= j < l < nums.len() implies nums[j] < nums[l] by {
                    if l < old_len as int {
                    } else {
                        assert(l == old_len as int);
                        assert(nums[l] == next);
                    }
                };
            }
        }

        (nums, lower, upper)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

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

fn sorted_to_deltas(vals: &[i32]) -> Vec<i32> {
    let mut deltas = Vec::new();
    for i in 1..vals.len() {
        deltas.push(vals[i] - vals[i - 1]);
    }
    deltas
}

fn random_deltas(rng: &mut Rng, n: usize, max_sum: i64) -> Vec<i32> {
    let mut deltas = Vec::new();
    let mut remaining = max_sum;
    for _ in 0..n {
        if remaining < 1 { break; }
        let max_d = std::cmp::min(remaining, 10000) as i32;
        let d = rng.gen_range_i64(1, max_d as i64) as i32;
        deltas.push(d);
        remaining -= d as i64;
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    macro_rules! emit {
        ($deltas:expr, $lower:expr, $upper:expr, $base:expr, $mk:expr) => {
            if emitted < count {
                let deltas_val: Vec<i32> = $deltas;
                let lower_val: i32 = $lower;
                let upper_val: i32 = $upper;
                let base_val: i32 = $base;
                let mk_val: u8 = $mk;
                let (nums_out, lower_out, upper_out) = generate_test_case(
                    &deltas_val, lower_val, upper_val, base_val, mk_val,
                );
                let result = Solution::find_missing_ranges(
                    nums_out.clone(), lower_out, upper_out,
                );
                let line = json!({
                    "input": {"nums": nums_out, "lower": lower_out, "upper": upper_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: nums=[0,1,3,50,75], lower=0, upper=99
    emit!(sorted_to_deltas(&[0, 1, 3, 50, 75]), 0, 99, 0, 0);
    // Example 2: nums=[-1], lower=-1, upper=-1
    emit!(vec![], -1, -1, -1, 0);

    // ---- Edge cases: empty array with all mutations ----
    for mk in [1u8, 2, 3, 4] {
        emit!(vec![], 0, 99, 50, mk);
        emit!(vec![], -1000000000, 1000000000, 0, mk);
    }

    // ---- Edge cases: single element ----
    emit!(vec![], 0, 0, 0, 0);                        // lower == upper, single elem
    emit!(vec![], -1000000000, 1000000000, -1000000000, 0); // single at min
    emit!(vec![], -1000000000, 1000000000, 1000000000, 0);  // single at max
    emit!(vec![], -1000000000, 1000000000, 0, 0);           // single at 0

    // ---- Edge cases: consecutive elements (dense, no gaps in nums) ----
    emit!(sorted_to_deltas(&[0, 1, 2, 3, 4]), 0, 4, 0, 0);   // full coverage
    emit!(sorted_to_deltas(&[0, 1, 2, 3, 4]), 0, 10, 0, 0);  // gap after
    emit!(sorted_to_deltas(&[5, 6, 7, 8, 9]), 0, 10, 5, 0);  // gaps before and after

    // ---- Edge cases: boundary values ----
    emit!(vec![], -1000000000, -1000000000, -1000000000, 0);
    emit!(vec![], 1000000000, 1000000000, 1000000000, 0);

    // ---- Random test cases ----
    while emitted < count {
        let size_class = emitted % 5;
        let n: usize = match size_class {
            0 => rng.gen_range_usize(0, 2),
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 20),
            3 => rng.gen_range_usize(20, 50),
            _ => rng.gen_range_usize(50, 100),
        };

        let lower = rng.gen_range_i64(-1000000000, 1000000000) as i32;
        let upper = rng.gen_range_i64(lower as i64, 1000000000) as i32;

        let base = rng.gen_range_i64(lower as i64, upper as i64) as i32;
        let max_sum = upper as i64 - base as i64;

        let num_deltas = if n == 0 { 0 } else { n - 1 };
        let deltas = random_deltas(&mut rng, num_deltas, max_sum);

        let mk = rng.gen_range_usize(0, 5) as u8;
        emit!(deltas, lower, upper, base, mk);
    }
}
