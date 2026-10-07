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
    base: i32,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        deltas.len() + 1 <= 10_000,
        -10_000 < base < 10_000,
        -10_000 < target < 10_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) < 10_000,
    ensures
        1 <= result.0.len() <= 10_000,
        -10_000 < result.1 < 10_000,
        forall|i: int| 0 <= i < result.0.len() ==> -10_000 < #[trigger] result.0[i] < 10_000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] < result.0[j],
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            nums.len() == i + 1,
            deltas.len() + 1 <= 10_000,
            -10_000 < base < 10_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) < 10_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= i as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> -10_000 < #[trigger] nums[k] < 10_000,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = nums[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(-10_000 < next < 10_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) < 10_000);
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] < next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        nums.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] < nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    // Compute mutated target before moving nums
    let mutated_target: i32 =
        if mutation_kind == 1 {
            nums[0]
        } else if mutation_kind == 2 {
            let last = nums.len() - 1;
            nums[last]
        } else if mutation_kind == 3 {
            let mid = nums.len() / 2;
            nums[mid]
        } else if mutation_kind == 4 && nums[0] > -9_999 {
            (nums[0] - 1) as i32
        } else if mutation_kind == 5 {
            let last = nums.len() - 1;
            if nums[last] < 9_999 {
                (nums[last] + 1) as i32
            } else {
                target
            }
        } else if mutation_kind == 6 && nums.len() >= 2 {
            if nums[1] - nums[0] > 1 {
                (nums[0] + 1) as i32
            } else {
                target
            }
        } else {
            target
        };

    (nums, mutated_target)
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

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range(1, max_d as i64) as i32);
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
    let mut rng = Rng::new(704);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let goal = 100usize;

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
                let result = Solution::search(nums_out.clone(), target_out);
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
    emit!(sorted_to_deltas(&[-1, 0, 3, 5, 9, 12]), -1, 9, 0);
    emit!(sorted_to_deltas(&[-1, 0, 3, 5, 9, 12]), -1, 2, 0);

    // ---- Single element with all applicable mutations ----
    for mk in 0u8..=6 {
        emit!(vec![], 0, 5, mk);
        emit!(vec![], -9999, 0, mk);
        emit!(vec![], 9999, 0, mk);
    }

    // ---- Two elements, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![1], 0, 5, mk);
        emit!(vec![9000], -4500, 0, mk);
    }

    // ---- Small arrays with consecutive deltas, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![2, 2, 2, 2], 1, 4, mk);   // [1,3,5,7,9]
    }

    // ---- Near boundaries, varied mutations ----
    emit!(vec![1,1,1,1,1,1,1,1,1], 9990, 9995, 0);
    emit!(vec![1,1,1,1,1,1,1,1,1], 9990, 9995, 1);
    emit!(vec![1,1,1,1,1,1,1,1,1], 9990, 9995, 2);
    emit!(vec![1,1,1,1,1,1,1,1,1], 9990, 9995, 3);
    emit!(vec![1,1,1,1,1,1,1,1,1], 9990, 9995, 4);
    emit!(vec![1,1,1,1,1,1,1,1,1], -9999, 0, 0);
    emit!(vec![1,1,1,1,1,1,1,1,1], -9999, 0, 2);
    emit!(vec![1,1,1,1,1,1,1,1,1], -9999, 0, 5);

    // ---- Consecutive spanning zero, varied mutations ----
    for mk in [0u8, 1, 2, 3, 4, 5] {
        emit!(vec![1; 100], -50, 0, mk);
    }

    // ---- Large gaps (deltas > 1) for mutation_kind == 6 ----
    emit!(vec![100, 100, 100], -500, 0, 6);
    emit!(vec![50, 50, 50, 50], 0, 0, 6);

    // ---- Random tiny arrays (2-5 elements), small deltas, all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range(2, 5) as usize;
        let deltas = random_deltas(&mut rng, n, 3);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let base = rng.gen_range(-9999, 9999i64.min(9999 - total)) as i32;
        let t = rng.gen_range(-9999, 9999) as i32;
        for mk in 0u8..=6 {
            emit!(deltas.clone(), base, t, mk);
        }
    }

    // ---- Random medium arrays (10-200 elements), mixed deltas, random mutations ----
    for _ in 0..6 {
        let n = rng.gen_range(10, 200) as usize;
        let max_d = std::cmp::max(1, (19998 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(9999i64, 9999 - total);
        let base = if hi < -9999 { -9999i32 } else { rng.gen_range(-9999, hi) as i32 };
        let t = rng.gen_range(-9999, 9999) as i32;
        let mk = (rng.gen_range(0, 6) as u8) % 7;
        emit!(deltas.clone(), base, t, mk);
        emit!(deltas.clone(), base, t, 0);
    }

    // ---- Random large arrays (500-5000 elements), delta=1, varied mutations ----
    for _ in 0..3 {
        let n = rng.gen_range(500, 5000) as usize;
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let hi = std::cmp::min(9999i64, 9999 - total);
        let base = if hi < -9999 { -9999i32 } else { rng.gen_range(-9999, hi) as i32 };
        let t = rng.gen_range(-9999, 9999) as i32;
        for mk in [0u8, 1, 2, 3] {
            emit!(deltas.clone(), base, t, mk);
        }
    }

    // ---- Maximum size (10000 elements), delta=1 ----
    {
        let deltas = vec![1i32; 9999];
        let base = -5000i32;
        emit!(deltas.clone(), base, 0, 0);
        emit!(deltas.clone(), base, 0, 1);
        emit!(deltas.clone(), base, 0, 2);
        emit!(deltas.clone(), base, 0, 3);
        emit!(deltas.clone(), base, 0, 4);
        emit!(deltas.clone(), base, 0, 5);
    }

    // ---- Large deltas (spread out), small arrays ----
    for _ in 0..3 {
        let n = rng.gen_range(2, 10) as usize;
        let max_d = std::cmp::max(1, (19998 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 1000));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(9999i64, 9999 - total);
        let base = if hi < -9999 { -9999i32 } else { rng.gen_range(-9999, hi) as i32 };
        let t = rng.gen_range(-9999, 9999) as i32;
        emit!(deltas.clone(), base, t, 6);
        emit!(deltas.clone(), base, t, 0);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let n = rng.gen_range(1, 500) as usize;
        let max_d = std::cmp::max(1, (19998 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(9999i64, 9999 - total);
        let base = if hi < -9999 { -9999i32 } else { rng.gen_range(-9999, hi) as i32 };
        let target = rng.gen_range(-9999, 9999) as i32;
        let mk = (rng.gen_range(0, 6) as u8) % 7;
        emit!(deltas, base, target, mk);
    }
}
