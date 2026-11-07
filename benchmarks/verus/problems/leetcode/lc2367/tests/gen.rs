use vstd::prelude::*;

verus! {

pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

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

proof fn lemma_sum_deltas_nonneg(deltas: Seq<i32>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, end) >= 0,
{
    lemma_sum_deltas_mono(deltas, 0, end);
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    diff: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= deltas.len() <= 199,
        0 <= base,
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 200,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        1 <= diff <= 50,
    ensures
        3 <= result.0.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 200,
        1 <= result.1 <= 50,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] < result.0[j],
{
    let mut nums: Vec<i32> = Vec::new();

    proof {
        lemma_sum_deltas_nonneg(deltas@, deltas.len() as int);
        assert(base <= 200) by {
            assert(base as int + sum_deltas(deltas@, deltas.len() as int) <= 200);
            assert(sum_deltas(deltas@, deltas.len() as int) >= 0);
        };
    }

    nums.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            nums.len() == idx + 1,
            2 <= deltas.len() <= 199,
            0 <= base,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 200,
            forall|k: int| 0 <= k < deltas.len() ==> 1 <= #[trigger] deltas[k],
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= idx as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 200,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
        decreases deltas.len() - idx,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = nums[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(0 <= next <= 200) by {
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int) <= 200);
                lemma_sum_deltas_nonneg(deltas@, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int >= 0);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] < next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        nums.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] < nums[l] by {
                if l < (nums.len() - 1) as int {
                } else {
                    assert(l == (nums.len() - 1) as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    let mutated_diff: i32 =
        if mutation_kind == 1 && diff < 50 {
            (diff + 1) as i32
        } else if mutation_kind == 2 && diff > 1 {
            (diff - 1) as i32
        } else if mutation_kind == 3 {
            1i32
        } else if mutation_kind == 4 {
            50i32
        } else if mutation_kind == 5 {
            25i32
        } else {
            diff
        };

    (nums, mutated_diff)
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

fn random_deltas_bounded(rng: &mut Rng, n: usize, max_total: i64) -> Vec<i32> {
    let num_deltas = n - 1;
    if num_deltas == 0 || max_total < num_deltas as i64 {
        return vec![1i32; num_deltas];
    }
    let mut deltas = Vec::new();
    let mut remaining = max_total;
    for i in 0..num_deltas {
        let left = (num_deltas - i - 1) as i64;
        let max_d = std::cmp::max(1, std::cmp::min(remaining - left, 200)) as i64;
        let d = rng.gen_range_i64(1, max_d) as i32;
        deltas.push(d);
        remaining -= d as i64;
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2367);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $diff:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let diff_val: i32 = $diff;
                let mk_val: u8 = $mk;
                let (nums_out, diff_out) = generate_test_case(
                    &deltas_val, base_val, diff_val, mk_val,
                );
                let result = Solution::arithmetic_triplets(nums_out.clone(), diff_out);
                let line = json!({
                    "input": {"nums": nums_out, "diff": diff_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // LeetCode examples
    emit!(sorted_to_deltas(&[0, 1, 4, 6, 7, 10]), 0, 3, 0);
    emit!(sorted_to_deltas(&[4, 5, 6, 7, 8, 9]), 4, 2, 0);

    // Minimum size (3 elements), all diff mutations
    for mk in 0u8..=5 {
        emit!(vec![1, 1], 0, 3, mk);
        emit!(vec![1, 1], 0, 1, mk);
        emit!(vec![50, 50], 0, 50, mk);
        emit!(vec![100, 100], 0, 10, mk);
    }

    // Small arrays with consecutive elements
    for mk in 0u8..=5 {
        emit!(vec![1, 1, 1, 1], 0, 1, mk);
        emit!(vec![2, 2, 2, 2], 0, 2, mk);
        emit!(vec![3, 3, 3, 3, 3], 0, 3, mk);
    }

    // Boundary values
    emit!(vec![1, 1], 198, 1, 0);
    emit!(vec![1, 1], 0, 1, 0);
    emit!(vec![1; 199], 0, 1, 0);
    emit!(vec![1; 199], 0, 1, 3);
    emit!(vec![1; 199], 0, 1, 4);

    // Arrays where no triplets exist
    emit!(vec![10, 10], 0, 3, 0);
    emit!(vec![1, 1, 1], 0, 5, 0);

    // Arrays where many triplets exist
    emit!(vec![2, 2, 2, 2, 2, 2, 2, 2, 2], 0, 2, 0);

    // Near max values
    for mk in 0u8..=5 {
        emit!(vec![1, 1], 197, 1, mk);
    }

    // Random tiny arrays (3-5 elements), all mutations
    for _ in 0..4 {
        let n = rng.gen_range_usize(3, 5);
        let base = rng.gen_range_i64(0, 50) as i32;
        let max_total = (200 - base) as i64;
        let deltas = random_deltas_bounded(&mut rng, n, max_total);
        let diff = rng.gen_range_i64(1, 50) as i32;
        for mk in 0u8..=5 {
            emit!(deltas.clone(), base, diff, mk);
        }
    }

    // Random small arrays (6-20 elements)
    for _ in 0..8 {
        let n = rng.gen_range_usize(6, 20);
        let base = rng.gen_range_i64(0, 50) as i32;
        let max_total = (200 - base) as i64;
        let deltas = random_deltas_bounded(&mut rng, n, max_total);
        let diff = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        emit!(deltas, base, diff, mk);
    }

    // Random medium arrays (21-100 elements)
    for _ in 0..8 {
        let n = rng.gen_range_usize(21, 100);
        let base = rng.gen_range_i64(0, 10) as i32;
        let max_total = (200 - base) as i64;
        let deltas = random_deltas_bounded(&mut rng, n, max_total);
        let diff = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        emit!(deltas, base, diff, mk);
    }

    // Random large arrays (101-200 elements)
    for _ in 0..6 {
        let n = rng.gen_range_usize(101, 200);
        let deltas = vec![1i32; n - 1];
        let base = rng.gen_range_i64(0, std::cmp::max(0, 200 - (n as i64 - 1))) as i32;
        let diff = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        emit!(deltas, base, diff, mk);
    }

    // Fill remaining with random sizes
    while count < goal {
        let n = rng.gen_range_usize(3, 50);
        let base = rng.gen_range_i64(0, 50) as i32;
        let max_total = (200 - base) as i64;
        let deltas = random_deltas_bounded(&mut rng, n, max_total);
        let diff = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        emit!(deltas, base, diff, mk);
    }
}
