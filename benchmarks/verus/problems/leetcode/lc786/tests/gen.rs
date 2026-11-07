use vstd::prelude::*;

verus! {

// ---- Spec fn helpers copied from spec.rs ----

pub open spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|d: int| 2 <= d < n ==> #[trigger](n % d) != 0
}

pub open spec fn fraction_less(s: Seq<i32>, a: int, b: int, num_idx: int, den_idx: int) -> bool {
    (s[a] as int) * (s[den_idx] as int) < (s[num_idx] as int) * (s[b] as int)
}

pub open spec fn count_less_inner(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int) -> nat
    decreases (s.len() - b) as nat
{
    if b >= s.len() {
        0nat
    } else if a >= b {
        0nat
    } else {
        let add = if fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat };
        add + count_less_inner(s, num_idx, den_idx, a, b + 1)
    }
}

pub open spec fn count_less_outer(s: Seq<i32>, num_idx: int, den_idx: int, a: int) -> nat
    decreases (s.len() - a) as nat
{
    if a >= s.len() {
        0nat
    } else {
        count_less_inner(s, num_idx, den_idx, a, a + 1)
            + count_less_outer(s, num_idx, den_idx, a + 1)
    }
}

pub open spec fn count_fractions_less(s: Seq<i32>, num_idx: int, den_idx: int) -> nat {
    count_less_outer(s, num_idx, den_idx, 0)
}

/// Spec function describing the array constructed from [1] ++ primes.
pub open spec fn arr_from_primes(primes: Seq<i32>) -> Seq<i32> {
    Seq::new(primes.len() + 1, |i: int| if i == 0 { 1i32 } else { primes[i - 1] })
}

// ---- Generator ----

pub fn generate_test_case(
    primes: &Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= primes.len() <= 999,
        forall|i: int| 0 <= i < primes.len() ==> 2 <= #[trigger] primes[i] <= 30_000,
        forall|i: int| 0 <= i < primes.len() ==> is_prime(#[trigger] primes[i] as int),
        forall|i: int, j: int| 0 <= i < j < primes.len() ==> primes[i] < primes[j],
        1 <= k <= ((primes.len() as int + 1) * primes.len() as int / 2),
        exists|i: int, j: int|
            0 <= i < j < primes.len() as int + 1
            && #[trigger] count_fractions_less(arr_from_primes(primes@), i, j)
                == (k - 1) as nat,
    ensures
        2 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 30_000,
        result.0[0] == 1,
        forall|i: int| 1 <= i < result.0.len() ==> #[trigger] is_prime(result.0[i] as int),
        forall|i: int, j: int|
            0 <= i < j < result.0.len() ==> result.0[i] < result.0[j],
        1 <= result.1 <= (result.0.len() * (result.0.len() - 1) / 2) as int,
        exists|i: int, j: int|
            0 <= i < j < result.0.len()
            && #[trigger] count_fractions_less(result.0@, i, j)
                == (result.1 - 1) as nat,
{
    // Build arr = [1] ++ primes
    let mut arr: Vec<i32> = Vec::new();
    arr.push(1i32);

    let mut idx: usize = 0;
    while idx < primes.len()
        invariant
            0 <= idx <= primes.len(),
            arr.len() == idx + 1,
            1 <= primes.len() <= 999,
            arr[0] == 1i32,
            forall|i: int| 0 <= i < primes.len() ==> 2 <= #[trigger] primes[i] <= 30_000,
            forall|i: int| 0 <= i < primes.len() ==> is_prime(#[trigger] primes[i] as int),
            forall|i: int, j: int| 0 <= i < j < primes.len() ==> primes[i] < primes[j],
            forall|p: int| 1 <= p < arr.len() ==> arr[p] == primes[p - 1],
            forall|p: int| 0 <= p < arr.len() ==> 1 <= #[trigger] arr[p] <= 30_000,
            forall|p: int| 1 <= p < arr.len() ==> is_prime(#[trigger] arr[p] as int),
            forall|p: int, q: int| 0 <= p < q < arr.len() ==> arr[p] < arr[q],
        decreases primes.len() - idx,
    {
        let v = primes[idx];

        proof {
            // v >= 2 > 1 = arr[0], and v > primes[idx-1] = arr[arr.len()-1] for idx > 0
            assert forall|p: int| 0 <= p < arr.len() implies arr[p] < v by {
                if p == 0 {
                    assert(arr[0] == 1);
                    assert(v >= 2);
                } else {
                    assert(arr[p] == primes[p - 1]);
                    assert(p - 1 < idx as int);
                    assert(primes[p - 1] < primes[idx as int]);
                }
            };
        }

        arr.push(v);
        idx += 1;
    }

    proof {
        // Prove arr@ =~= arr_from_primes(primes@) by extensional equality
        assert(arr.len() == primes.len() + 1);
        assert forall|i: int| 0 <= i < arr.len() implies arr@[i] == arr_from_primes(primes@)[i] by {
            if i == 0 {
                assert(arr@[0] == 1);
                assert(arr_from_primes(primes@)[0] == 1);
            } else {
                assert(arr@[i] == primes@[i - 1]);
                assert(arr_from_primes(primes@)[i] == primes@[i - 1]);
            }
        };
        assert(arr@ =~= arr_from_primes(primes@));
    }

    (arr, k)
}

} // verus!

// ---- Unverified main: sampling + output ----

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

/// All primes up to 30000 (sieve of Eratosthenes).
fn sieve_primes(limit: usize) -> Vec<i32> {
    let mut is_prime = vec![true; limit + 1];
    is_prime[0] = false;
    if limit >= 1 { is_prime[1] = false; }
    let mut i = 2;
    while i * i <= limit {
        if is_prime[i] {
            let mut j = i * i;
            while j <= limit {
                is_prime[j] = false;
                j += i;
            }
        }
        i += 1;
    }
    is_prime.iter().enumerate()
        .filter(|(_, &b)| b)
        .map(|(i, _)| i as i32)
        .collect()
}

/// For a given arr (sorted, starting with 1, then primes), enumerate all
/// fractions arr[i]/arr[j] (i < j), sort them, and return a Vec mapping
/// rank (1-based) to the (i, j) pair.
fn fraction_ranks(arr: &[i32]) -> Vec<(usize, usize)> {
    let n = arr.len();
    let mut fractions: Vec<(f64, usize, usize)> = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            fractions.push((arr[i] as f64 / arr[j] as f64, i, j));
        }
    }
    fractions.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    fractions.iter().map(|&(_, i, j)| (i, j)).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(786);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let all_primes = sieve_primes(30_000);

    macro_rules! emit {
        ($primes:expr, $k:expr) => {
            if emitted < count {
                let primes_val: Vec<i32> = $primes;
                let k_val: i32 = $k;
                let (arr_out, k_out) = generate_test_case(&primes_val, k_val, 0);
                let result = Solution::kth_smallest_prime_fraction(arr_out.clone(), k_out);
                let line = json!({
                    "input": {"arr": arr_out, "k": k_out},
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
    emit!(vec![2, 3, 5], 3);            // arr = [1,2,3,5], k=3 -> [2,5]
    emit!(vec![7], 1);                   // arr = [1,7], k=1 -> [1,7]

    // ---- Edge cases: 2 elements (1 prime), k=1 ----
    emit!(vec![2], 1);
    emit!(vec![29989], 1);               // large prime near 30000

    // ---- Small arrays, all valid k values ----
    {
        let small_primes = vec![2, 3, 5];  // arr = [1,2,3,5], 6 fractions
        let max_k = (small_primes.len() + 1) * small_primes.len() / 2;
        for k in 1..=(max_k as i32) {
            emit!(small_primes.clone(), k);
        }
    }
    {
        let small_primes = vec![2, 3, 5, 7, 11]; // arr len 6, 15 fractions
        let max_k = (small_primes.len() + 1) * small_primes.len() / 2;
        for k in 1..=(max_k as i32) {
            emit!(small_primes.clone(), k);
        }
    }

    // ---- Boundary primes ----
    emit!(vec![2, 3], 1);
    emit!(vec![2, 3], 2);
    emit!(vec![2, 3], 3);

    // ---- Two large primes ----
    emit!(vec![29989, 29999], 1);
    emit!(vec![29989, 29999], 2);
    emit!(vec![29989, 29999], 3);

    // ---- Diverse size classes ----
    let size_classes: Vec<usize> = vec![2, 3, 5, 10, 20, 50, 100, 200, 500, 999];
    for &n_primes in &size_classes {
        if emitted >= count { break; }
        let n_primes = n_primes.min(all_primes.len());
        // Select n_primes primes: first n_primes
        let primes_subset: Vec<i32> = all_primes[..n_primes].to_vec();
        let max_k = (n_primes + 1) * n_primes / 2;
        // k = 1 (smallest fraction)
        emit!(primes_subset.clone(), 1);
        // k = max (largest fraction)
        emit!(primes_subset.clone(), max_k as i32);
        // k = middle
        emit!(primes_subset.clone(), (max_k / 2).max(1) as i32);
        // random k
        let rk = rng.gen_range_usize(1, max_k) as i32;
        emit!(primes_subset.clone(), rk);
    }

    // ---- Random subsets of primes with diverse sizes and k values ----
    while emitted < count {
        // Pick a size class
        let n_primes = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(100, 999.min(all_primes.len())),
        };
        let n_primes = n_primes.min(all_primes.len());

        // Select n_primes random primes (sorted)
        let mut indices: Vec<usize> = Vec::new();
        if n_primes >= all_primes.len() {
            indices = (0..all_primes.len()).collect();
        } else {
            // Reservoir-style: pick random starting point and stride
            let start = rng.gen_range_usize(0, all_primes.len() - n_primes);
            let stride = (all_primes.len() - start) / n_primes;
            let stride = stride.max(1);
            let mut pos = start;
            for _ in 0..n_primes {
                if pos >= all_primes.len() { break; }
                indices.push(pos);
                pos += stride;
            }
        }
        if indices.is_empty() { continue; }

        let primes_subset: Vec<i32> = indices.iter().map(|&i| all_primes[i]).collect();
        let max_k = (primes_subset.len() + 1) * primes_subset.len() / 2;
        if max_k == 0 { continue; }

        // Pick k: mix of boundary and random values
        let k = match emitted % 5 {
            0 => 1i32,
            1 => max_k as i32,
            2 => (max_k / 2).max(1) as i32,
            _ => rng.gen_range_usize(1, max_k) as i32,
        };

        emit!(primes_subset, k);
    }
}
