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

/// Build a non-increasing array: arr[0] = base, arr[k+1] = arr[k] - deltas[k].
fn build_non_increasing(base: i32, deltas: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= base <= 100_000,
        deltas.len() < 100_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int - sum_deltas(deltas@, deltas.len() as int) >= 1,
    ensures
        result.len() == deltas.len() + 1,
        result.len() <= 100_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 100_000,
        forall|a: int, b: int| 0 <= a < b < result.len()
            ==> (#[trigger] result[a]) >= (#[trigger] result[b]),
{
    let mut arr: Vec<i32> = Vec::new();
    arr.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            arr.len() == idx + 1,
            deltas.len() < 100_000,
            1 <= base <= 100_000,
            forall|j: int| 0 <= j < deltas.len() ==> 0 <= #[trigger] deltas[j],
            base as int - sum_deltas(deltas@, deltas.len() as int) >= 1,
            forall|k: int| 0 <= k <= idx as int
                ==> (#[trigger] arr[k]) as int == base as int - sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < arr.len() ==> 1 <= #[trigger] arr[k] <= 100_000,
            forall|a: int, b: int| 0 <= a < b < arr.len()
                ==> (#[trigger] arr[a]) >= (#[trigger] arr[b]),
        decreases deltas.len() - idx,
    {
        let ghost old_len = arr.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
            lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
        }

        let next = arr[idx] - deltas[idx];

        proof {
            assert(next as int == base as int - sum_deltas(deltas@, (idx + 1) as int));
            assert(next >= 1i32) by {
                assert(sum_deltas(deltas@, (idx + 1) as int)
                    <= sum_deltas(deltas@, deltas.len() as int));
                assert(next as int >= base as int - sum_deltas(deltas@, deltas.len() as int));
            };
            assert(next <= 100_000i32) by {
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0int);
                assert(next as int <= base as int);
            };

            assert forall|k: int| 0 <= k < arr.len()
                implies arr[k] >= next by {
                assert(arr[k] as int == base as int - sum_deltas(deltas@, k));
                assert(next as int == base as int - sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_mono(deltas@, k, (idx + 1) as int);
            };
        }

        arr.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int| 0 <= k <= idx as int
                implies (#[trigger] arr[k]) as int
                    == base as int - sum_deltas(deltas@, k) by {
                if k < idx as int {
                } else {
                    assert(arr[k] == next);
                }
            };

            assert forall|a: int, b: int| 0 <= a < b < arr.len()
                implies (#[trigger] arr[a]) >= (#[trigger] arr[b]) by {
                if b < old_len as int {
                } else {
                    assert(b == old_len as int);
                    assert(arr[b] == next);
                }
            };
        }
    }

    arr
}

/// Build a constant (all-same-value) non-increasing array.
fn build_constant(val: i32, len: usize) -> (result: Vec<i32>)
    requires
        1 <= val <= 100_000,
        1 <= len <= 100_000,
    ensures
        result.len() == len,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 100_000,
        forall|a: int, b: int| 0 <= a < b < result.len()
            ==> (#[trigger] result[a]) >= (#[trigger] result[b]),
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            arr.len() == i,
            1 <= val <= 100_000,
            forall|k: int| 0 <= k < arr.len() ==> #[trigger] arr[k] == val,
        decreases len - i,
    {
        arr.push(val);
        i = i + 1;
    }

    proof {
        assert forall|k: int| 0 <= k < arr.len()
            implies 1 <= #[trigger] arr[k] <= 100_000 by {
            assert(arr[k] == val);
        };
        assert forall|a: int, b: int| 0 <= a < b < arr.len()
            implies (#[trigger] arr[a]) >= (#[trigger] arr[b]) by {
            assert(arr[a] == val);
            assert(arr[b] == val);
        };
    }

    arr
}

pub fn generate_test_case(
    base1: i32,
    deltas1: &Vec<i32>,
    base2: i32,
    deltas2: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= base1 <= 100_000,
        1 <= base2 <= 100_000,
        deltas1.len() < 100_000,
        deltas2.len() < 100_000,
        forall|i: int| 0 <= i < deltas1.len() ==> 0 <= #[trigger] deltas1[i],
        forall|i: int| 0 <= i < deltas2.len() ==> 0 <= #[trigger] deltas2[i],
        base1 as int - sum_deltas(deltas1@, deltas1.len() as int) >= 1,
        base2 as int - sum_deltas(deltas2@, deltas2.len() as int) >= 1,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |k: int| 0 <= k < result.0.len() ==> 1 <= #[trigger] result.0[k] <= 100_000,
        forall |k: int| 0 <= k < result.1.len() ==> 1 <= #[trigger] result.1[k] <= 100_000,
        forall |a: int, b: int| 0 <= a < b < result.0.len() ==> (#[trigger] result.0[a]) >= (#[trigger] result.0[b]),
        forall |a: int, b: int| 0 <= a < b < result.1.len() ==> (#[trigger] result.1[a]) >= (#[trigger] result.1[b]),
{
    if mutation_kind == 1 {
        // single-element nums1
        let mut nums1: Vec<i32> = Vec::new();
        nums1.push(base1);
        let nums2 = build_non_increasing(base2, deltas2);
        (nums1, nums2)
    } else if mutation_kind == 2 {
        // single-element nums2
        let nums1 = build_non_increasing(base1, deltas1);
        let mut nums2: Vec<i32> = Vec::new();
        nums2.push(base2);
        (nums1, nums2)
    } else if mutation_kind == 3 {
        // constant nums1 (all base1), normal nums2
        let len1 = (deltas1.len() + 1) as usize;
        let nums1 = build_constant(base1, len1);
        let nums2 = build_non_increasing(base2, deltas2);
        (nums1, nums2)
    } else if mutation_kind == 4 {
        // normal nums1, constant nums2 (all base2)
        let nums1 = build_non_increasing(base1, deltas1);
        let len2 = (deltas2.len() + 1) as usize;
        let nums2 = build_constant(base2, len2);
        (nums1, nums2)
    } else if mutation_kind == 5 {
        // both constant
        let len1 = (deltas1.len() + 1) as usize;
        let len2 = (deltas2.len() + 1) as usize;
        let nums1 = build_constant(base1, len1);
        let nums2 = build_constant(base2, len2);
        (nums1, nums2)
    } else {
        // normal build (mutation_kind == 0 and fallback)
        let nums1 = build_non_increasing(base1, deltas1);
        let nums2 = build_non_increasing(base2, deltas2);
        (nums1, nums2)
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

/// Generate a vector of non-negative deltas whose sum <= budget.
fn random_deltas(rng: &mut Rng, n: usize, budget: i64) -> Vec<i32> {
    let mut deltas = Vec::new();
    let mut remaining = budget;
    for _ in 0..n {
        let max_d = std::cmp::min(remaining, 100_000) as i64;
        let d = if max_d > 0 { rng.gen_range_i64(0, max_d) as i32 } else { 0 };
        deltas.push(d);
        remaining -= d as i64;
    }
    deltas
}

/// Convert a non-increasing array to (base, deltas) form.
fn to_base_deltas(arr: &[i32]) -> (i32, Vec<i32>) {
    let base = arr[0];
    let mut deltas = Vec::new();
    for i in 1..arr.len() {
        deltas.push(arr[i - 1] - arr[i]);
    }
    (base, deltas)
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1855);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    macro_rules! emit {
        ($n1:expr, $n2:expr) => {
            if total < count {
                let nums1: Vec<i32> = $n1;
                let nums2: Vec<i32> = $n2;
                let result = Solution::max_distance(nums1.clone(), nums2.clone());
                writeln!(out, "{}", json!({
                    "input": {"nums1": nums1, "nums2": nums2},
                    "output": result
                })).unwrap();
                total += 1;
            }
        };
    }

    // ---- Example test cases from description.md ----
    emit!(vec![55, 30, 5, 4, 2], vec![100, 20, 10, 10, 5]);
    emit!(vec![2, 2, 2], vec![10, 10, 1]);
    emit!(vec![30, 29, 19, 5], vec![25, 25, 25, 25, 25]);

    // ---- Edge cases ----
    // Single element arrays
    emit!(vec![1], vec![1]);
    emit!(vec![100_000], vec![100_000]);
    emit!(vec![1], vec![100_000]);
    emit!(vec![100_000], vec![1]);

    // All same values
    emit!(vec![5, 5, 5, 5], vec![5, 5, 5, 5]);
    emit!(vec![1, 1, 1], vec![100_000; 5]);
    emit!(vec![100_000; 5], vec![1, 1, 1]);

    // nums1 > nums2 everywhere (distance = 0)
    emit!(vec![10, 9, 8], vec![7, 6, 5]);

    // nums1 <= nums2 everywhere (max distance = min(n1, n2) - 1 or n2 - 1)
    emit!(vec![5, 4, 3], vec![10, 9, 8, 7, 6]);

    // ---- Generated via verified generator, all mutation kinds ----
    macro_rules! gen_emit {
        ($b1:expr, $d1:expr, $b2:expr, $d2:expr, $mk:expr) => {
            if total < count {
                let d1: Vec<i32> = $d1;
                let d2: Vec<i32> = $d2;
                let (nums1, nums2) = generate_test_case($b1, &d1, $b2, &d2, $mk);
                let result = Solution::max_distance(nums1.clone(), nums2.clone());
                writeln!(out, "{}", json!({
                    "input": {"nums1": nums1, "nums2": nums2},
                    "output": result
                })).unwrap();
                total += 1;
            }
        };
    }

    // Specific patterns with all mutation kinds
    for mk in 0u8..=5 {
        gen_emit!(55, vec![25, 25, 1, 2], 100, vec![80, 10, 0, 5], mk);
    }
    for mk in 0u8..=5 {
        gen_emit!(10, vec![0, 0, 0], 10, vec![0, 0, 0, 0], mk);
    }
    for mk in 0u8..=5 {
        gen_emit!(100_000, vec![1; 10], 100_000, vec![1; 10], mk);
    }

    // ---- Tiny arrays (1-5 elements), varied mutations ----
    for _ in 0..6 {
        let n1 = rng.gen_range_usize(0, 4);
        let n2 = rng.gen_range_usize(0, 4);
        let base1 = rng.gen_range_i64(1, 100_000) as i32;
        let base2 = rng.gen_range_i64(1, 100_000) as i32;
        let d1 = random_deltas(&mut rng, n1, (base1 - 1) as i64);
        let d2 = random_deltas(&mut rng, n2, (base2 - 1) as i64);
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        gen_emit!(base1, d1, base2, d2, mk);
    }

    // ---- Small arrays (5-20 elements) ----
    for _ in 0..6 {
        let n1 = rng.gen_range_usize(4, 19);
        let n2 = rng.gen_range_usize(4, 19);
        let base1 = rng.gen_range_i64(1, 100_000) as i32;
        let base2 = rng.gen_range_i64(1, 100_000) as i32;
        let d1 = random_deltas(&mut rng, n1, (base1 - 1) as i64);
        let d2 = random_deltas(&mut rng, n2, (base2 - 1) as i64);
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        gen_emit!(base1, d1, base2, d2, mk);
    }

    // ---- Medium arrays (20-200 elements) ----
    for _ in 0..6 {
        let n1 = rng.gen_range_usize(19, 199);
        let n2 = rng.gen_range_usize(19, 199);
        let base1 = rng.gen_range_i64(1, 100_000) as i32;
        let base2 = rng.gen_range_i64(1, 100_000) as i32;
        let d1 = random_deltas(&mut rng, n1, (base1 - 1) as i64);
        let d2 = random_deltas(&mut rng, n2, (base2 - 1) as i64);
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        gen_emit!(base1, d1, base2, d2, mk);
    }

    // ---- Large arrays (200-5000 elements) ----
    for _ in 0..4 {
        let n1 = rng.gen_range_usize(199, 4999);
        let n2 = rng.gen_range_usize(199, 4999);
        let base1 = rng.gen_range_i64(1, 100_000) as i32;
        let base2 = rng.gen_range_i64(1, 100_000) as i32;
        let d1 = random_deltas(&mut rng, n1, (base1 - 1) as i64);
        let d2 = random_deltas(&mut rng, n2, (base2 - 1) as i64);
        gen_emit!(base1, d1, base2, d2, 0);
    }

    // ---- Near-boundary values ----
    gen_emit!(100_000, vec![0; 99], 100_000, vec![0; 99], 0);
    gen_emit!(1, vec![0; 99], 1, vec![0; 99], 0);
    gen_emit!(100_000, vec![99_999], 1, vec![0], 0);
    gen_emit!(1, vec![0], 100_000, vec![99_999], 0);

    // ---- Steeply decreasing arrays ----
    gen_emit!(100_000, vec![10_000, 10_000, 10_000, 10_000, 10_000, 10_000, 10_000, 10_000, 10_000],
              100_000, vec![10_000, 10_000, 10_000, 10_000, 10_000, 10_000, 10_000, 10_000, 10_000], 0);

    // ---- Fill remaining with random sizes and random mutations ----
    while total < count {
        let size_class = rng.gen_range_usize(0, 4);
        let (n1, n2) = match size_class {
            0 => (rng.gen_range_usize(0, 4), rng.gen_range_usize(0, 4)),
            1 => (rng.gen_range_usize(4, 19), rng.gen_range_usize(4, 19)),
            2 => (rng.gen_range_usize(19, 199), rng.gen_range_usize(19, 199)),
            3 => (rng.gen_range_usize(199, 4999), rng.gen_range_usize(199, 4999)),
            _ => (rng.gen_range_usize(4999, 99_999), rng.gen_range_usize(4999, 99_999)),
        };
        let base1 = rng.gen_range_i64(1, 100_000) as i32;
        let base2 = rng.gen_range_i64(1, 100_000) as i32;
        let d1 = random_deltas(&mut rng, n1, (base1 - 1) as i64);
        let d2 = random_deltas(&mut rng, n2, (base2 - 1) as i64);
        let mk = (rng.gen_range_i64(0, 5) as u8) % 6;
        gen_emit!(base1, d1, base2, d2, mk);
    }

    eprintln!("Generated {} test cases -> {:?}", total, out_path);
}
