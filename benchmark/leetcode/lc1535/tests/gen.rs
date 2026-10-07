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
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        deltas.len() >= 1,
        deltas.len() + 1 <= 100_000,
        1 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        2 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        1 <= result.1 <= 1_000_000_000,
{
    let mut arr: Vec<i32> = Vec::new();
    arr.push(base);

    proof {
        assert(arr[0] == base);
        assert(sum_deltas(deltas@, 0) == 0);
        assert(arr[0] as int == base as int + sum_deltas(deltas@, 0));
        assert(1 <= base <= 1_000_000) by {
            lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        };
    }

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            arr.len() == idx + 1,
            deltas.len() + 1 <= 100_000,
            1 <= base,
            forall|m: int| 0 <= m < deltas.len() ==> #[trigger] deltas[m] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000,
            forall|m: int| 0 <= m <= idx as int ==>
                #[trigger] arr[m] == (base as int + sum_deltas(deltas@, m)) as i32,
            forall|m: int| 0 <= m <= idx as int ==>
                arr[m] as int == base as int + sum_deltas(deltas@, m),
            forall|m: int| 0 <= m < arr.len() ==> 1 <= #[trigger] arr[m] <= 1_000_000,
            forall|m: int, n: int| 0 <= m < n < arr.len() ==> arr[m] < arr[n],
        decreases deltas.len() - idx,
    {
        let ghost old_len = arr.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = arr[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(1 <= next <= 1_000_000) by {
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
            };

            assert forall|m: int| 0 <= m < arr.len() implies arr[m] < next by {
                assert(arr[m] as int == base as int + sum_deltas(deltas@, m));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_strict(deltas@, m, (idx + 1) as int);
            };
        }

        arr.push(next);
        idx = idx + 1;

        proof {
            assert forall|m: int, n: int| 0 <= m < n < arr.len() implies arr[m] < arr[n] by {
                if n < old_len as int {
                } else {
                    assert(n == old_len as int);
                    assert(arr[n] == next);
                }
            };
        }
    }

    // Apply k mutation
    let mutated_k = if mutation_kind == 0 {
        k
    } else if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        1_000_000_000i32
    } else if mutation_kind == 3 && k < 1_000_000_000 {
        k + 1
    } else if mutation_kind == 4 && k > 1 {
        k - 1
    } else {
        k
    };

    // Prove distinctness from strict ordering
    proof {
        assert forall|i: int, j: int| 0 <= i < j < arr.len() implies arr[i] != arr[j] by {
            assert(arr[i] < arr[j]);
        };
    }

    (arr, mutated_k)
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

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(1, max_d as i64) as i32);
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1535);
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $k:expr, $mk:expr) => {
            if count < count_goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let k_val: i32 = $k;
                let mk_val: u8 = $mk;
                let (arr_out, k_out) = generate_test_case(
                    &deltas_val, base_val, k_val, mk_val,
                );
                let result = Solution::get_winner(arr_out.clone(), k_out);
                let line = json!({
                    "input": {"arr": arr_out, "k": k_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples from description.md ----
    emit!(sorted_to_deltas(&[1, 2, 3, 4, 5, 6, 7]), 1, 2, 0);
    emit!(sorted_to_deltas(&[1, 2, 3]), 1, 10, 0);

    // ---- Single pair (minimum size), all k mutations ----
    for mk in 0u8..=4 {
        emit!(vec![1], 1, 5, mk);
        emit!(vec![1], 999_999, 1, mk);
        emit!(vec![500_000], 1, 100, mk);
    }

    // ---- Small arrays with consecutive deltas (all 1), all mutations ----
    for mk in 0u8..=4 {
        emit!(vec![1, 1, 1, 1], 1, 3, mk);
        emit!(vec![1, 1, 1, 1, 1, 1], 1, 1, mk);
        emit!(vec![1, 1, 1, 1, 1, 1], 1, 100, mk);
    }

    // ---- Boundary k values with small arrays ----
    emit!(vec![1, 1, 1], 1, 1, 0);
    emit!(vec![1, 1, 1], 1, 1_000_000_000, 0);

    // ---- Near value boundaries ----
    emit!(vec![1, 1, 1, 1], 999_996, 2, 0);
    emit!(vec![1, 1, 1], 1, 3, 0);

    // ---- Large gaps between elements ----
    emit!(vec![100_000, 100_000, 100_000], 1, 2, 0);
    emit!(vec![200_000, 200_000], 1, 1, 0);
    emit!(vec![500_000], 1, 1, 0);

    // ---- Arithmetic progressions with varied step sizes ----
    emit!(vec![10; 10], 1, 5, 0);
    emit!(vec![100; 5], 1, 3, 0);
    emit!(vec![1000; 3], 1, 2, 0);

    // ---- Random tiny arrays (2-5 elements), all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(2, 5);
        let max_d = std::cmp::max(1, (1_000_000i64 / n as i64) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 1000));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        for mk in 0u8..=4 {
            emit!(deltas.clone(), base, k, mk);
        }
    }

    // ---- Random medium arrays (10-200 elements), mixed deltas ----
    for _ in 0..8 {
        let n = rng.gen_range_usize(10, 200);
        let max_d = std::cmp::max(1, (999_999i64 / n as i64) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.gen_range_usize(0, 4) as u8) % 5;
        emit!(deltas.clone(), base, k, mk);
        emit!(deltas.clone(), base, k, 0);
    }

    // ---- Random large arrays (500-5000 elements), delta=1 ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(500, 5000);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        for mk in [0u8, 1, 2, 3] {
            emit!(deltas.clone(), base, k, mk);
        }
    }

    // ---- Maximum size arrays ----
    {
        let deltas = vec![1i32; 99_999];
        let base = 1i32;
        emit!(deltas.clone(), base, 50_000, 0);
        emit!(deltas.clone(), base, 50_000, 1);
        emit!(deltas.clone(), base, 50_000, 2);
        emit!(deltas.clone(), base, 1, 0);
        emit!(deltas.clone(), base, 1_000_000_000, 0);
    }

    // ---- k = n-1 (exact full pass), varied sizes ----
    for n in [3usize, 5, 10, 50, 100] {
        let deltas = vec![1i32; n - 1];
        emit!(deltas.clone(), 1, (n - 1) as i32, 0);
    }

    // ---- k much larger than n (max element always wins) ----
    for n in [2usize, 5, 20] {
        let deltas = vec![1i32; n - 1];
        emit!(deltas.clone(), 1, 1_000_000_000, 0);
    }

    // ---- Large value gaps with small arrays ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(2, 10);
        let max_d = std::cmp::max(1, (999_999i64 / n as i64) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100_000));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let k = rng.gen_range_i64(1, 100) as i32;
        emit!(deltas.clone(), base, k, 0);
        emit!(deltas.clone(), base, k, 2);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < count_goal {
        let n = rng.gen_range_usize(2, 500);
        let max_d = std::cmp::max(1, (999_999i64 / std::cmp::max(n, 1) as i64) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.gen_range_usize(0, 4) as u8) % 5;
        emit!(deltas, base, k, mk);
    }
}
