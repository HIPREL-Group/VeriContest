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

pub open spec fn is_rotation_point(nums: Seq<i32>, k: int) -> bool {
    0 <= k < nums.len()
    && (forall |a: int, b: int| k <= a < b < nums.len() ==> nums[a] <= nums[b])
    && (forall |a: int, b: int| 0 <= a < b < k ==> nums[a] <= nums[b])
    && (k == 0 || forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() ==> nums[a] >= nums[b])
}

pub fn generate_test_case(
        deltas: &Vec<i32>,
        base: i32,
        k: usize,
        mutation_kind: u8,
    ) -> (result: Vec<i32>)
        requires
            0 <= deltas.len() <= 4999,
            -5000 <= base <= 5000,
            forall |i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 5000,
            0 <= k <= deltas.len(),
        ensures
            1 <= result.len() <= 5000,
            forall |i: int| 0 <= i < result.len() ==> -5000 <= #[trigger] result[i] <= 5000,
            exists |k: int| is_rotation_point(result@, k),
    {
        let n: usize = deltas.len() + 1;

        // --- Mutation 2: all-equal array ---
        if mutation_kind == 2 {
            let mut result: Vec<i32> = Vec::new();
            let mut idx: usize = 0;
            while idx < n
                invariant
                    0 <= idx <= n,
                    result.len() == idx,
                    1 <= n <= 5000,
                    -5000 <= base <= 5000,
                    forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == base,
                decreases n - idx,
            {
                result.push(base);
                idx += 1;
            }

            proof {
                assert(result.len() == n);
                assert(1 <= result.len() <= 5000);

                assert forall|i: int| 0 <= i < result.len()
                    implies -5000 <= #[trigger] result[i] <= 5000 by
                {
                    assert(result[i] == base);
                };

                assert forall|a: int, b: int| 0 <= a < b < result.len() as int
                    implies result[a] <= result[b] by
                {
                    assert(result[a] == base);
                    assert(result[b] == base);
                };
                assert(is_rotation_point(result@, 0int));
            }

            return result;
        }

        // Effective rotation point
        let ek: usize = if mutation_kind == 1 { 0 } else { k };

        // Step 1: Build sorted non-decreasing array from base + cumulative deltas
        let mut sorted_arr: Vec<i32> = Vec::new();
        sorted_arr.push(base);

        let mut i: usize = 0;
        while i < deltas.len()
            invariant
                0 <= i <= deltas.len(),
                sorted_arr.len() == i + 1,
                n == deltas.len() + 1,
                -5000 <= base <= 5000,
                forall|j: int| 0 <= j < deltas.len() ==> 0 <= #[trigger] deltas[j],
                base as int + sum_deltas(deltas@, deltas.len() as int) <= 5000,
                forall|j: int| 0 <= j <= i as int ==>
                    (#[trigger] sorted_arr[j]) as int == base as int + sum_deltas(deltas@, j),
                forall|j: int| 0 <= j < sorted_arr.len() ==>
                    -5000 <= #[trigger] sorted_arr[j] <= 5000,
                forall|j: int, l: int| 0 <= j < l < sorted_arr.len() ==>
                    sorted_arr[j] <= sorted_arr[l],
            decreases deltas.len() - i,
        {
            proof {
                lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, 0) == 0int);
            }

            let next = sorted_arr[i] + deltas[i];

            proof {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));

                assert(-5000 <= next <= 5000) by {
                    lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
                    lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                    assert(sum_deltas(deltas@, 0) == 0int);
                };

                assert forall|j: int| 0 <= j < sorted_arr.len()
                    implies sorted_arr[j] <= next by
                {
                    lemma_sum_deltas_mono(deltas@, j, (i + 1) as int);
                };
            }

            sorted_arr.push(next);
            i += 1;
        }

        // sorted_arr: length n, sorted non-decreasing, elements in [-5000, 5000]

        // Step 2: Build rotated result = sorted_arr[ek..n) ++ sorted_arr[0..ek)
        let mut result: Vec<i32> = Vec::new();

        // Copy sorted_arr[ek..n)
        let mut j: usize = ek;
        while j < n
            invariant
                ek <= j <= n,
                0 <= ek <= n,
                n == deltas.len() + 1,
                sorted_arr.len() == n,
                result.len() == j - ek,
                forall|idx: int| 0 <= idx < result.len() ==>
                    #[trigger] result[idx] == sorted_arr[ek as int + idx],
                forall|idx: int| 0 <= idx < sorted_arr.len() ==>
                    -5000 <= #[trigger] sorted_arr[idx] <= 5000,
                forall|idx: int, l: int| 0 <= idx < l < sorted_arr.len() ==>
                    sorted_arr[idx] <= sorted_arr[l],
            decreases n - j,
        {
            result.push(sorted_arr[j]);
            j += 1;
        }

        let fpl: usize = n - ek; // first-part length

        // Copy sorted_arr[0..ek)
        let mut j2: usize = 0;
        while j2 < ek
            invariant
                0 <= j2 <= ek,
                0 <= ek <= n,
                n == deltas.len() + 1,
                sorted_arr.len() == n,
                fpl == n - ek,
                result.len() == fpl + j2,
                forall|idx: int| 0 <= idx < fpl as int ==>
                    #[trigger] result[idx] == sorted_arr[ek as int + idx],
                forall|idx: int| fpl as int <= idx < result.len() ==>
                    #[trigger] result[idx] == sorted_arr[idx - fpl as int],
                forall|idx: int| 0 <= idx < sorted_arr.len() ==>
                    -5000 <= #[trigger] sorted_arr[idx] <= 5000,
                forall|idx: int, l: int| 0 <= idx < l < sorted_arr.len() ==>
                    sorted_arr[idx] <= sorted_arr[l],
            decreases ek - j2,
        {
            result.push(sorted_arr[j2]);
            j2 += 1;
        }

        // Prove ensures
        proof {
            assert(result.len() == n);
            assert(1 <= result.len() <= 5000);

            // Element bounds
            assert forall|i: int| 0 <= i < result.len()
                implies -5000 <= #[trigger] result[i] <= 5000 by
            {
                if i < fpl as int {
                    assert(result[i] == sorted_arr[ek as int + i]);
                } else {
                    assert(result[i] == sorted_arr[i - fpl as int]);
                }
            };

            // Rotation point proof
            if ek == 0 {
                // No rotation: result == sorted_arr, rotation point = 0
                assert forall|a: int, b: int| 0 <= a < b < result.len() as int
                    implies result[a] <= result[b] by
                {
                    assert(result[a] == sorted_arr[a]);
                    assert(result[b] == sorted_arr[b]);
                };
                assert(is_rotation_point(result@, 0int));
            } else {
                let rp: int = fpl as int;
                assert(0 < rp);
                assert(rp < result.len());

                // From rp to end: result[rp..n] = sorted_arr[0..ek], sorted
                assert forall|a: int, b: int| rp <= a < b < result.len() as int
                    implies result[a] <= result[b] by
                {
                    assert(result[a] == sorted_arr[a - rp]);
                    assert(result[b] == sorted_arr[b - rp]);
                    assert(0 <= a - rp);
                    assert(a - rp < b - rp);
                    assert(b - rp < sorted_arr.len());
                };

                // From 0 to rp: result[0..rp] = sorted_arr[ek..n], sorted
                assert forall|a: int, b: int| 0 <= a < b < rp
                    implies result[a] <= result[b] by
                {
                    assert(result[a] == sorted_arr[ek as int + a]);
                    assert(result[b] == sorted_arr[ek as int + b]);
                    assert(0 <= ek as int + a);
                    assert(ek as int + a < ek as int + b);
                    assert(ek as int + b < sorted_arr.len());
                };

                // Cross: elements [0..rp) >= elements [rp..n)
                assert forall|a: int, b: int|
                    0 <= a < rp && rp <= b < result.len() as int
                    implies result[a] >= result[b] by
                {
                    assert(result[a] == sorted_arr[ek as int + a]);
                    assert(result[b] == sorted_arr[b - rp]);
                    assert(0 <= b - rp);
                    assert(b - rp < ek as int);
                    assert(ek as int <= ek as int + a);
                    assert(ek as int + a < sorted_arr.len());
                    // b - rp < ek <= ek + a, so sorted_arr[b - rp] <= sorted_arr[ek + a]
                    assert(sorted_arr[b - rp] <= sorted_arr[ek as int + a]);
                };

                assert(is_rotation_point(result@, rp));
            }
        }

        result
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

/// Build a Vec<i32> of non-negative deltas that sum to at most `budget`,
/// with each delta in [0, max_delta]. Length = `n`.
fn make_deltas(rng: &mut Rng, n: usize, budget: i64, max_delta: i64) -> Vec<i32> {
    let mut deltas = Vec::with_capacity(n);
    let mut remaining = budget;
    for _ in 0..n {
        let cap = remaining.min(max_delta).max(0);
        let d = if cap > 0 { rng.gen_range_i64(0, cap) } else { 0 };
        deltas.push(d as i32);
        remaining -= d;
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let mut rng = Rng::new(seed);

    macro_rules! emit {
        ($deltas:expr, $base:expr, $k:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let k_val: usize = $k;
                let mk_val: u8 = $mk;
                let nums = generate_test_case(&deltas_val, base_val, k_val, mk_val);
                let result = Solution::find_min(nums.clone());
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

    // ---- Example inputs from description.md ----
    // [1, 3, 5] => deltas [2, 2], base 1, k=0 (no rotation)
    emit!(vec![2, 2], 1, 0, 0);
    // [2, 2, 2, 0, 1] => sorted [0,1,2,2,2], deltas [1,1,0,0], base 0, k=2
    emit!(vec![1, 1, 0, 0], 0, 2, 0);

    // ---- Boundary: single element (no deltas) ----
    emit!(vec![], 0, 0, 0);
    emit!(vec![], -5000, 0, 0);
    emit!(vec![], 5000, 0, 0);

    // ---- Boundary: two elements ----
    emit!(vec![1], 1, 0, 0);   // [1, 2] no rotation
    emit!(vec![1], 1, 1, 0);   // [2, 1] rotated
    emit!(vec![0], 1, 0, 0);   // [1, 1] equal

    // ---- All-equal arrays (mutation_kind 2) ----
    for mk in [2u8] {
        emit!(vec![0; 9], 3, 0, mk);
        emit!(vec![0; 99], 0, 0, mk);
        emit!(vec![0; 4], -5000, 0, mk);
        emit!(vec![0; 4], 5000, 0, mk);
    }

    // ---- Fully sorted (no rotation, mutation_kind 1 forces k=0) ----
    emit!(vec![1000, 1000, 1000, 1000], -5000, 0, 1);
    emit!(vec![1, 1, 1, 1, 1, 1, 1, 1, 1], 1, 0, 1);

    // ---- Hardcoded seed pool with all mutation kinds ----
    for mk in 0u8..=2 {
        emit!(vec![1, 2, 3, 4], -10, 2, mk);
        emit!(vec![5, 5, 5], 0, 1, mk);
        emit!(vec![0, 0, 0, 10], -100, 3, mk);
    }

    // ---- Random tiny arrays (1-5 elements) ----
    for _ in 0..8 {
        let n = rng.gen_range_usize(1, 5);
        let nd = if n > 0 { n - 1 } else { 0 };
        let base = rng.gen_range_i64(-5000, 5000) as i32;
        let budget = 5000i64 - base as i64;
        let deltas = make_deltas(&mut rng, nd, budget.max(0), 100);
        let k = if nd > 0 { rng.gen_range_usize(0, nd) } else { 0 };
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }

    // ---- Random small arrays (6-20 elements) ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(6, 20);
        let nd = n - 1;
        let base = rng.gen_range_i64(-5000, 4000) as i32;
        let budget = 5000i64 - base as i64;
        let deltas = make_deltas(&mut rng, nd, budget.max(0), 50);
        let k = rng.gen_range_usize(0, nd);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }

    // ---- Random medium arrays (21-200 elements) ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(21, 200);
        let nd = n - 1;
        let base = rng.gen_range_i64(-5000, 3000) as i32;
        let budget = 5000i64 - base as i64;
        let max_d = std::cmp::max(1, (10000 / n) as i64);
        let deltas = make_deltas(&mut rng, nd, budget.max(0), max_d);
        let k = rng.gen_range_usize(0, nd);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }

    // ---- Random large arrays (201-2000 elements) ----
    for _ in 0..8 {
        let n = rng.gen_range_usize(201, 2000);
        let nd = n - 1;
        let base = rng.gen_range_i64(-5000, 0) as i32;
        let budget = 5000i64 - base as i64;
        let max_d = std::cmp::max(1, (10000 / n) as i64);
        let deltas = make_deltas(&mut rng, nd, budget.max(0), max_d);
        let k = rng.gen_range_usize(0, nd);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }

    // ---- Maximum size arrays (4000-5000 elements) ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(4000, 5000);
        let nd = n - 1;
        let base = rng.gen_range_i64(-5000, -3000) as i32;
        let budget = 5000i64 - base as i64;
        let max_d = std::cmp::max(1, (10000 / n) as i64);
        let deltas = make_deltas(&mut rng, nd, budget.max(0), max_d);
        let k = rng.gen_range_usize(0, nd);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }

    // ---- All-equal random arrays (mutation_kind 2) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(1, 500);
        let nd = if n > 0 { n - 1 } else { 0 };
        let val = rng.gen_range_i64(-5000, 5000) as i32;
        emit!(vec![0i32; nd], val, 0, 2);
    }

    // ---- Arrays with many duplicates (deltas mostly 0) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(5, 100);
        let nd = n - 1;
        let base = rng.gen_range_i64(-5000, 4990) as i32;
        let budget = 5000i64 - base as i64;
        let deltas = make_deltas(&mut rng, nd, budget.max(0), 1);
        let k = rng.gen_range_usize(0, nd);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }

    // ---- Fill remaining with random sizes and rotations ----
    let mut _attempts = 0usize;
    while count < goal {
        _attempts += 1;
        if _attempts > 10000 { break; }
        let n = rng.gen_range_usize(1, 1000);
        let nd = if n > 0 { n - 1 } else { 0 };
        let base = rng.gen_range_i64(-5000, 4000) as i32;
        let budget = 5000i64 - base as i64;
        let max_d = std::cmp::max(1, (10000i64 / n as i64));
        let deltas = make_deltas(&mut rng, nd, budget.max(0), max_d);
        let k = if nd > 0 { rng.gen_range_usize(0, nd) } else { 0 };
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(deltas, base, k, mk);
    }
}
