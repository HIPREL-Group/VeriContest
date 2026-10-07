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

/// Two partial sums are non-strictly ordered when every delta >= 0.
proof fn lemma_sum_deltas_nondec(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_nondec(deltas, a, b - 1);
    }
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    k_param: i32,
    x: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        deltas.len() + 1 <= 10000,
        -10000 <= base <= 10000,
        -10000 <= x <= 10000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 10000,
        1 <= k_param <= (deltas.len() + 1) as i32,
    ensures
        1 <= result.1 <= result.0.len() as i32,
        1 <= result.0.len() <= 10000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
        forall|i: int| 0 <= i < result.0.len() ==> -10000 <= #[trigger] result.0[i] <= 10000,
        -10000 <= result.2 <= 10000,
{
    let mut arr: Vec<i32> = Vec::new();
    arr.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            arr.len() == i + 1,
            deltas.len() + 1 <= 10000,
            -10000 <= base <= 10000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 0i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 10000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] arr[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= i as int ==>
                arr[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < arr.len() ==> -10000 <= #[trigger] arr[k] <= 10000,
            forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] <= arr[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = arr.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = arr[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(-10000 <= next <= 10000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 10000);
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
            };

            assert forall|k: int| 0 <= k < arr.len() implies arr[k] <= next by {
                assert(arr[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_nondec(deltas@, k, (i + 1) as int);
            };
        }

        arr.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < arr.len() implies arr[k] <= arr[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(arr[l] == next);
                }
            };
        }
    }

    // Apply mutations to x
    let mutated_x: i32 =
        if mutation_kind == 1 {
            arr[0]
        } else if mutation_kind == 2 {
            let last = arr.len() - 1;
            arr[last]
        } else if mutation_kind == 3 {
            let mid = arr.len() / 2;
            arr[mid]
        } else if mutation_kind == 4 && arr[0] > -10000 {
            (arr[0] - 1) as i32
        } else if mutation_kind == 5 {
            let last = arr.len() - 1;
            if arr[last] < 10000 {
                (arr[last] + 1) as i32
            } else {
                x
            }
        } else if mutation_kind == 6 {
            -10000i32
        } else if mutation_kind == 7 {
            10000i32
        } else if mutation_kind == 8 {
            0i32
        } else {
            x
        };

    // Apply mutations to k
    let n = arr.len() as i32;
    let mutated_k: i32 =
        if mutation_kind == 9 {
            1i32
        } else if mutation_kind == 10 {
            n
        } else if mutation_kind == 11 {
            let half = n / 2;
            if half >= 1 { half } else { 1i32 }
        } else {
            k_param
        };

    (arr, mutated_k, mutated_x)
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
        deltas.push(rng.gen_range_i64(0, max_d as i64) as i32);
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(658);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $k:expr, $x:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let k_val: i32 = $k;
                let x_val: i32 = $x;
                let mk_val: u8 = $mk;
                let (arr_out, k_out, x_out) = generate_test_case(
                    &deltas_val, base_val, k_val, x_val, mk_val,
                );
                let result = Solution::find_closest_elements(arr_out.clone(), k_out, x_out);
                let line = json!({
                    "input": {"arr": arr_out, "k": k_out, "x": x_out},
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
    emit!(sorted_to_deltas(&[1, 2, 3, 4, 5]), 1, 4, 3, 0);
    emit!(sorted_to_deltas(&[1, 1, 2, 3, 4, 5]), 1, 4, -1, 0);

    // ---- Single element, all applicable mutations ----
    for mk in 0u8..=11 {
        emit!(vec![], 0, 1, 5, mk);
        emit!(vec![], -10000, 1, 0, mk);
        emit!(vec![], 10000, 1, 0, mk);
    }

    // ---- Two elements, varied mutations ----
    for mk in 0u8..=11 {
        emit!(vec![1], 0, 1, 5, mk);
        emit!(vec![0], 5, 2, 5, mk);  // duplicates allowed
        emit!(vec![5000], -5000, 1, 0, mk);
    }

    // ---- Small arrays with consecutive deltas, all mutations ----
    for mk in 0u8..=11 {
        emit!(vec![1, 1, 1, 1], 1, 3, 3, mk);       // [1,2,3,4,5], k=3
        emit!(vec![0, 0, 0, 0], 5, 2, 5, mk);        // [5,5,5,5,5], all same
    }

    // ---- k = 1, k = n edge cases ----
    emit!(vec![1, 2, 3, 4], 0, 1, 2, 0);   // k=1
    emit!(vec![1, 2, 3, 4], 0, 5, 2, 0);   // k=n

    // ---- Boundary values for x ----
    emit!(vec![1, 1, 1], -9999, 2, -10000, 0);   // x = min
    emit!(vec![1, 1, 1], 9997, 2, 10000, 0);     // x = max
    emit!(vec![1, 1, 1], 0, 2, 0, 0);            // x = 0

    // ---- Random tiny arrays (2-5 elements), small deltas, all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(2, 5);
        let deltas = random_deltas(&mut rng, n, 3);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let x = rng.gen_range_i64(-10000, 10000) as i32;
        for mk in 0u8..=11 {
            emit!(deltas.clone(), base, k, x, mk);
        }
    }

    // ---- Random medium arrays (10-200 elements), mixed deltas, random mutations ----
    for _ in 0..8 {
        let n = rng.gen_range_usize(10, 200);
        let max_d = std::cmp::max(1, (20000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let x = rng.gen_range_i64(-10000, 10000) as i32;
        let mk = (rng.gen_range_usize(0, 11) as u8) % 12;
        emit!(deltas.clone(), base, k, x, mk);
        emit!(deltas.clone(), base, k, x, 0);
    }

    // ---- Random large arrays (500-5000 elements), delta=1, varied mutations ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(500, 5000);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let hi = std::cmp::min(10000i64, 10000 - total);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let x = rng.gen_range_i64(-10000, 10000) as i32;
        for mk in [0u8, 1, 2, 3, 9, 10] {
            emit!(deltas.clone(), base, k, x, mk);
        }
    }

    // ---- Maximum size (10000 elements), delta=1 ----
    {
        let deltas = vec![1i32; 9999];
        let base = -5000i32;
        let k = 500;
        emit!(deltas.clone(), base, k, 0, 0);
        emit!(deltas.clone(), base, k, 0, 1);
        emit!(deltas.clone(), base, k, 0, 2);
        emit!(deltas.clone(), base, k, 0, 3);
        emit!(deltas.clone(), base, k, 0, 9);
        emit!(deltas.clone(), base, k, 0, 10);
    }

    // ---- Arrays with all-same elements (delta=0) ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(2, 50);
        let deltas = vec![0i32; n - 1];
        let base = rng.gen_range_i64(-10000, 10000) as i32;
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let x = rng.gen_range_i64(-10000, 10000) as i32;
        for mk in [0u8, 1, 2, 8, 9, 10] {
            emit!(deltas.clone(), base, k, x, mk);
        }
    }

    // ---- Fill remaining with random sizes and mutations ----
    while count < goal {
        let n = rng.gen_range_usize(1, 500);
        let max_d = std::cmp::max(1, (20000 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let x = rng.gen_range_i64(-10000, 10000) as i32;
        let mk = (rng.gen_range_usize(0, 11) as u8) % 12;
        emit!(deltas, base, k, x, mk);
    }
}
