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
        1 <= deltas.len() + 1 <= 1000,
        1 <= base,
        1 <= k <= 1000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1 <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] < result.0[j],
{
    // Build sorted array from base + cumulative deltas
    let mut arr: Vec<i32> = Vec::new();

    proof {
        // sum_deltas(deltas@, 0) == 0, so base <= 1000
        assert(sum_deltas(deltas@, 0) == 0int);
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(base as int + 0 <= base as int + sum_deltas(deltas@, deltas.len() as int));
        assert(base as int <= 1000);
    }

    arr.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            arr.len() == i + 1,
            deltas.len() + 1 <= 1000,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] arr[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= i as int ==>
                arr[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < arr.len() ==> 1 <= #[trigger] arr[k] <= 1000,
            forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = arr.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = arr[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(1 <= next <= 1000) by {
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int >= 1);
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(next as int <= 1000);
            };

            assert forall|k: int| 0 <= k < arr.len() implies arr[k] < next by {
                assert(arr[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        arr.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < arr.len() implies arr[k] < arr[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(arr[l] == next);
                }
            };
        }
    }

    // Apply mutations to k
    let mutated_k: i32 =
        if mutation_kind == 1 && k < 1000 {
            (k + 1) as i32          // nudge up
        } else if mutation_kind == 2 && k > 1 {
            (k - 1) as i32          // nudge down
        } else if mutation_kind == 3 {
            1i32                    // min boundary
        } else if mutation_kind == 4 {
            1000i32                 // max boundary
        } else if mutation_kind == 5 {
            if k >= 2 { (k / 2) as i32 } else { k }  // halve
        } else if mutation_kind == 6 && k <= 500 {
            (k * 2) as i32          // double
        } else {
            k                       // identity / fallback
        };

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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $k:expr, $mk:expr) => {{
            let (arr, k) = generate_test_case(&$deltas, $base, $k, $mk);
            let key = format!("{:?}|{}", arr, k);
            if seen.insert(key) {
                let result = Solution::find_kth_positive(arr.clone(), k);
                writeln!(out, "{}", json!({
                    "input": {"arr": arr, "k": k},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }};
    }

    // ---- Example inputs from description.md ----
    // Example 1: arr = [2,3,4,7,11], k = 5 -> 9
    emit!(vec![1, 1, 3, 4], 2, 5, 0);
    // Example 2: arr = [1,2,3,4], k = 2 -> 6
    emit!(vec![1, 1, 1], 1, 2, 0);

    // ---- Boundary: single element arrays ----
    emit!(Vec::<i32>::new(), 1, 1, 0);       // arr=[1], k=1
    emit!(Vec::<i32>::new(), 1, 1000, 0);    // arr=[1], k=1000
    emit!(Vec::<i32>::new(), 1000, 1, 0);    // arr=[1000], k=1
    emit!(Vec::<i32>::new(), 500, 500, 0);   // arr=[500], k=500

    // ---- Boundary: k = 1 and k = 1000 across mutation kinds ----
    for mk in 0u8..=6 {
        emit!(vec![1, 1, 1, 1], 1, 1, mk);
        emit!(vec![1, 1, 1, 1], 1, 1000, mk);
    }

    // ---- Consecutive arrays (delta=1), various sizes ----
    // arr = [1,2,...,n], missing numbers start at n+1
    for &n in &[2usize, 5, 10, 50, 100, 500] {
        if n <= 1000 {
            let deltas = vec![1i32; n - 1];
            let k_val = std::cmp::min(1000, (n as i32) + 1);
            for mk in 0u8..=6 {
                emit!(deltas.clone(), 1, k_val, mk);
            }
        }
    }

    // ---- Sparse arrays (large deltas), many missing numbers ----
    for &n in &[2usize, 5, 10] {
        let max_d = std::cmp::min(999 / std::cmp::max(n, 1), 100) as i32;
        if max_d >= 2 {
            let deltas: Vec<i32> = vec![max_d; n - 1];
            let total: i64 = deltas.iter().map(|d| *d as i64).sum();
            if 1 + total <= 1000 {
                for mk in 0u8..=6 {
                    emit!(deltas.clone(), 1, 5, mk);
                }
            }
        }
    }

    // ---- Random tiny arrays (1-5 elements), all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(1, 5);
        let deltas = random_deltas(&mut rng, n, 3);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(1000i64, 1000 - total);
        let base = if max_base < 1 { 1 } else { rng.gen_range_i64(1, max_base) as i32 };
        let k = rng.gen_range_i64(1, 1000) as i32;
        for mk in 0u8..=6 {
            emit!(deltas.clone(), base, k, mk);
        }
    }

    // ---- Random medium arrays (10-100 elements), mixed deltas, random mutations ----
    for _ in 0..8 {
        let n = rng.gen_range_usize(10, 100);
        let max_d = std::cmp::max(1, (999 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(1000i64, 1000 - total);
        let base = if max_base < 1 { 1 } else { rng.gen_range_i64(1, max_base) as i32 };
        let k = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.gen_range_i64(0, 6) as u8) % 7;
        emit!(deltas.clone(), base, k, mk);
        emit!(deltas.clone(), base, k, 0);
    }

    // ---- Random large arrays (200-999 elements), delta=1 ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(200, 999);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let max_base = std::cmp::min(1000i64, 1000 - total);
        let base = if max_base < 1 { 1 } else { rng.gen_range_i64(1, max_base) as i32 };
        let k = rng.gen_range_i64(1, 1000) as i32;
        for mk in [0u8, 1, 2, 3, 4] {
            emit!(deltas.clone(), base, k, mk);
        }
    }

    // ---- Maximum size (1000 elements), delta=1 ----
    {
        let deltas = vec![1i32; 999];
        emit!(deltas.clone(), 1, 1, 0);
        emit!(deltas.clone(), 1, 1000, 0);
        emit!(deltas.clone(), 1, 500, 0);
        emit!(deltas.clone(), 1, 1, 3);
        emit!(deltas.clone(), 1, 1, 4);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let n = rng.gen_range_usize(1, 500);
        let max_d = std::cmp::max(1, (999 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 20));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(1000i64, 1000 - total);
        let base = if max_base < 1 { 1 } else { rng.gen_range_i64(1, max_base) as i32 };
        let k = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.gen_range_i64(0, 6) as u8) % 7;
        emit!(deltas, base, k, mk);
    }
}
