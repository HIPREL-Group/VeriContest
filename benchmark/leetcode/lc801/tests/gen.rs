use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_a: Vec<i32>, raw_b: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures 2 <= result.0.len() <= 100000, result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 200000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 200000,
        forall|i: int| 1 <= i < result.0.len() ==>
            ((#[trigger] result.0[i] > result.0[i - 1] && result.1[i] > result.1[i - 1])
            || (result.0[i] > result.1[i - 1] && result.1[i] > result.0[i - 1])),
{
    let n = if raw_a.len() < 2 { 2usize } else if raw_a.len() > 100000 { 100000usize } else { raw_a.len() };
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();
    let mut low_previous = -1i32;
    let mut high_previous = -1i32;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 100000, a.len() == i, b.len() == i,
            -1 <= low_previous <= high_previous <= 200000 - (n - i),
            i == 0 ==> low_previous == -1 && high_previous == -1,
            i > 0 ==> ((low_previous == a[i - 1] && high_previous == b[i - 1])
                || (low_previous == b[i - 1] && high_previous == a[i - 1])),
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] a[j] <= 200000,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] b[j] <= 200000,
            forall|j: int| 1 <= j < i ==>
                ((#[trigger] a[j] > a[j - 1] && b[j] > b[j - 1])
                || (a[j] > b[j - 1] && b[j] > a[j - 1])),
        decreases n - i,
    {
        let x = if i < raw_a.len() { raw_a[i] } else { 0 };
        let y = if i < raw_b.len() { raw_b[i] } else { 0 };
        let swapped = x > y;
        let low = if x < y { x } else { y };
        let high = if x < y { y } else { x };
        let ceiling = 200000 - ((n - i - 1) as i32);
        let low = if low <= low_previous { low_previous + 1 } else if low > ceiling { ceiling } else { low };
        let high = if high <= high_previous { high_previous + 1 } else if high > ceiling { ceiling } else { high };
        let high = if high < low { low } else { high };
        a.push(if swapped { high } else { low });
        b.push(if swapped { low } else { high });
        low_previous = low;
        high_previous = high;
        i += 1;
    }
    (a, b)
}


/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is non-negative when every delta >= 1.
proof fn lemma_sum_deltas_nonneg(deltas: Seq<i32>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_deltas_nonneg(deltas, end - 1);
    }
}

/// sum_deltas is monotonically non-decreasing when every delta >= 1.
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

/// Build two arrays of equal length from delta vectors and base values.
/// Construction: nums[k] = base + sum(deltas[0..k]) for each array.
/// Mutation kinds swap elements between the two arrays at specific positions,
/// producing inputs where the two sequences are not individually increasing
/// but can be made increasing by swapping back.
pub fn generate_candidate(
    deltas1: &Vec<i32>,
    deltas2: &Vec<i32>,
    base1: i32,
    base2: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= deltas1.len() <= 99_999,
        deltas1.len() == deltas2.len(),
        0 <= base1,
        0 <= base2,
        forall|i: int| 0 <= i < deltas1.len() ==> 1 <= #[trigger] deltas1[i],
        forall|i: int| 0 <= i < deltas2.len() ==> 1 <= #[trigger] deltas2[i],
        base1 as int + sum_deltas(deltas1@, deltas1.len() as int) <= i32::MAX as int,
        base2 as int + sum_deltas(deltas2@, deltas2.len() as int) <= i32::MAX as int,
    ensures
        2 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==>
            0 <= #[trigger] result.0[i],
        forall|i: int| 0 <= i < result.1.len() ==>
            0 <= #[trigger] result.1[i],
{
    let mut nums1: Vec<i32> = Vec::new();
    let mut nums2: Vec<i32> = Vec::new();

    nums1.push(base1);
    nums2.push(base2);

    let mut cum1: i32 = base1;
    let mut cum2: i32 = base2;

    let mut i: usize = 0;
    while i < deltas1.len()
        invariant
            0 <= i <= deltas1.len(),
            nums1.len() == i + 1,
            nums2.len() == i + 1,
            1 <= deltas1.len() <= 99_999,
            deltas1.len() == deltas2.len(),
            0 <= base1,
            0 <= base2,
            forall|k: int| 0 <= k < deltas1.len() ==> 1 <= #[trigger] deltas1[k],
            forall|k: int| 0 <= k < deltas2.len() ==> 1 <= #[trigger] deltas2[k],
            base1 as int + sum_deltas(deltas1@, deltas1.len() as int) <= i32::MAX as int,
            base2 as int + sum_deltas(deltas2@, deltas2.len() as int) <= i32::MAX as int,
            cum1 as int == base1 as int + sum_deltas(deltas1@, i as int),
            cum2 as int == base2 as int + sum_deltas(deltas2@, i as int),
            cum1 >= 0,
            cum2 >= 0,
            forall|k: int| 0 <= k < nums1.len() ==> 0 <= #[trigger] nums1[k],
            forall|k: int| 0 <= k < nums2.len() ==> 0 <= #[trigger] nums2[k],
        decreases deltas1.len() - i,
    {
        proof {
            lemma_sum_deltas_mono(deltas1@, (i + 1) as int, deltas1.len() as int);
            lemma_sum_deltas_mono(deltas2@, (i + 1) as int, deltas2.len() as int);
            lemma_sum_deltas_nonneg(deltas1@, (i + 1) as int);
            lemma_sum_deltas_nonneg(deltas2@, (i + 1) as int);
        }

        let next1 = cum1 + deltas1[i];
        let next2 = cum2 + deltas2[i];

        proof {
            assert(next1 as int == base1 as int + sum_deltas(deltas1@, (i + 1) as int));
            assert(next2 as int == base2 as int + sum_deltas(deltas2@, (i + 1) as int));
            assert(next1 >= 0) by {
                lemma_sum_deltas_nonneg(deltas1@, (i + 1) as int);
            };
            assert(next2 >= 0) by {
                lemma_sum_deltas_nonneg(deltas2@, (i + 1) as int);
            };
        }

        nums1.push(next1);
        nums2.push(next2);
        cum1 = next1;
        cum2 = next2;
        i = i + 1;
    }

    // Post-construction mutations: swap elements between arrays at specific
    // positions.  Since every element in both arrays is >= 0, exchanging two
    // values preserves non-negativity.
    if mutation_kind == 1 {
        // Swap last pair
        let last = nums1.len() - 1;
        let t1 = nums1[last];
        let t2 = nums2[last];
        nums1.set(last, t2);
        nums2.set(last, t1);
        proof {
            assert forall|k: int| 0 <= k < nums1.len()
                implies 0 <= #[trigger] nums1[k] by {
                if k == last as int { assert(nums1[k] == t2); }
            };
            assert forall|k: int| 0 <= k < nums2.len()
                implies 0 <= #[trigger] nums2[k] by {
                if k == last as int { assert(nums2[k] == t1); }
            };
        }
    } else if mutation_kind == 2 {
        // Swap first pair
        let t1 = nums1[0];
        let t2 = nums2[0];
        nums1.set(0, t2);
        nums2.set(0, t1);
        proof {
            assert forall|k: int| 0 <= k < nums1.len()
                implies 0 <= #[trigger] nums1[k] by {
                if k == 0int { assert(nums1[k] == t2); }
            };
            assert forall|k: int| 0 <= k < nums2.len()
                implies 0 <= #[trigger] nums2[k] by {
                if k == 0int { assert(nums2[k] == t1); }
            };
        }
    } else if mutation_kind == 3 {
        // Swap middle pair
        let mid = nums1.len() / 2;
        let t1 = nums1[mid];
        let t2 = nums2[mid];
        nums1.set(mid, t2);
        nums2.set(mid, t1);
        proof {
            assert forall|k: int| 0 <= k < nums1.len()
                implies 0 <= #[trigger] nums1[k] by {
                if k == mid as int { assert(nums1[k] == t2); }
            };
            assert forall|k: int| 0 <= k < nums2.len()
                implies 0 <= #[trigger] nums2[k] by {
                if k == mid as int { assert(nums2[k] == t1); }
            };
        }
    } else if mutation_kind == 4 {
        // Swap all pairs (full reversal of roles)
        let mut j: usize = 0;
        while j < nums1.len()
            invariant
                0 <= j <= nums1.len(),
                nums1.len() == nums2.len(),
                nums1.len() == deltas1.len() + 1,
                forall|k: int| 0 <= k < nums1.len() ==> 0 <= #[trigger] nums1[k],
                forall|k: int| 0 <= k < nums2.len() ==> 0 <= #[trigger] nums2[k],
            decreases nums1.len() - j,
        {
            let t1 = nums1[j];
            let t2 = nums2[j];
            nums1.set(j, t2);
            nums2.set(j, t1);
            proof {
                assert forall|k: int| 0 <= k < nums1.len()
                    implies 0 <= #[trigger] nums1[k] by {
                    if k == j as int { assert(nums1[k] == t2); }
                };
                assert forall|k: int| 0 <= k < nums2.len()
                    implies 0 <= #[trigger] nums2[k] by {
                    if k == j as int { assert(nums2[k] == t1); }
                };
            }
            j = j + 1;
        }
    } else if mutation_kind == 5 {
        // Boundary: set first elements to 0
        nums1.set(0, 0i32);
        nums2.set(0, 0i32);
        proof {
            assert forall|k: int| 0 <= k < nums1.len()
                implies 0 <= #[trigger] nums1[k] by {
                if k == 0int { assert(nums1[k] == 0i32); }
            };
            assert forall|k: int| 0 <= k < nums2.len()
                implies 0 <= #[trigger] nums2[k] by {
                if k == 0int { assert(nums2[k] == 0i32); }
            };
        }
    }
    // mutation_kind 0 or default: no mutation

    (nums1, nums2)
}

} // verus!

// ---------------------------------------------------------------------------
// Unverified main: sampling, running code.rs, writing JSONL
// ---------------------------------------------------------------------------

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

/// Build a random delta vector of length `n` with values in [1, max_d].
fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i64(1, max_d as i64) as i32).collect()
}

/// Compute the sum of a delta vector (as i64 to avoid overflow).
fn delta_sum(deltas: &[i32]) -> i64 {
    deltas.iter().map(|d| *d as i64).sum()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(801);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit_raw {
        ($n1:expr, $n2:expr) => {
            if count < goal {
                let nums1_val: Vec<i32> = $n1;
                let nums2_val: Vec<i32> = $n2;
                let (nums1_val, nums2_val) = generate_test_case(nums1_val, nums2_val);
                let result = Solution::min_swap(nums1_val.clone(), nums2_val.clone());
                let line = json!({
                    "input": {"nums1": nums1_val, "nums2": nums2_val},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    macro_rules! emit {
        ($d1:expr, $d2:expr, $b1:expr, $b2:expr, $mk:expr) => {
            if count < goal {
                let d1_val: Vec<i32> = $d1;
                let d2_val: Vec<i32> = $d2;
                let b1_val: i32 = $b1;
                let b2_val: i32 = $b2;
                let mk_val: u8 = $mk;
                let (nums1_val, nums2_val) = generate_candidate(
                    &d1_val, &d2_val, b1_val, b2_val, mk_val,
                );
                let (nums1_val, nums2_val) = generate_test_case(nums1_val, nums2_val);
                let result = Solution::min_swap(nums1_val.clone(), nums2_val.clone());
                let line = json!({
                    "input": {"nums1": nums1_val, "nums2": nums2_val},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples (directly, not through generator) ----
    emit_raw!(vec![1, 3, 5, 4], vec![1, 2, 3, 7]);
    emit_raw!(vec![0, 3, 5, 8, 9], vec![2, 1, 4, 6, 7]);

    // ---- Minimal arrays (n=2), all mutations ----
    for mk in 0u8..=5 {
        emit!(vec![1], vec![1], 0, 0, mk);
        emit!(vec![1], vec![2], 0, 1, mk);
        emit!(vec![5], vec![3], 1, 2, mk);
        emit!(vec![100], vec![50], 0, 0, mk);
    }

    // ---- Small arrays (n=3-5), all mutations ----
    for mk in 0u8..=5 {
        emit!(vec![2, 2], vec![1, 1], 1, 1, mk);         // [1,3,5] [1,2,3]
        emit!(vec![2, 2, 2], vec![1, 1, 1], 1, 1, mk);   // [1,3,5,7] [1,2,3,4]
        emit!(vec![1, 1, 1, 1], vec![1, 1, 1, 1], 0, 0, mk);
    }

    // ---- Arrays with large gaps between elements ----
    for mk in [0u8, 1, 3] {
        emit!(vec![1000, 1000, 1000], vec![500, 500, 500], 0, 0, mk);
        emit!(vec![100, 200, 300], vec![50, 100, 150], 10, 20, mk);
    }

    // ---- Arrays starting at boundary 0 ----
    for mk in [0u8, 1, 2, 5] {
        emit!(vec![1, 1, 1, 1, 1], vec![1, 1, 1, 1, 1], 0, 0, mk);
    }

    // ---- Medium arrays (10-50 elements), random deltas ----
    for _ in 0..8 {
        let n = rng.gen_range_usize(10, 50);
        let max_d = 100i32;
        let d1 = random_deltas(&mut rng, n - 1, max_d);
        let d2 = random_deltas(&mut rng, n - 1, max_d);
        let b1 = rng.gen_range_i64(0, 1000) as i32;
        let b2 = rng.gen_range_i64(0, 1000) as i32;
        for mk in 0u8..=4 {
            emit!(d1.clone(), d2.clone(), b1, b2, mk);
        }
    }

    // ---- Larger arrays (100-500 elements), small deltas ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(100, 500);
        let d1 = random_deltas(&mut rng, n - 1, 5);
        let d2 = random_deltas(&mut rng, n - 1, 5);
        let b1 = rng.gen_range_i64(0, 100) as i32;
        let b2 = rng.gen_range_i64(0, 100) as i32;
        let mk = rng.gen_range_i64(0, 5) as u8;
        emit!(d1, d2, b1, b2, mk);
    }

    // ---- Large arrays (1000-5000 elements), delta=1 (consecutive) ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1000, 5000);
        let d1 = vec![1i32; n - 1];
        let d2 = vec![1i32; n - 1];
        let b1 = rng.gen_range_i64(0, 50) as i32;
        let b2 = rng.gen_range_i64(0, 50) as i32;
        for mk in [0u8, 1, 3, 4] {
            emit!(d1.clone(), d2.clone(), b1, b2, mk);
        }
    }

    // ---- Near-maximum arrays (10000 elements), delta=1 ----
    {
        let n = 10_000usize;
        let d1 = vec![1i32; n - 1];
        let d2 = vec![1i32; n - 1];
        emit!(d1.clone(), d2.clone(), 0, 0, 0);
        emit!(d1.clone(), d2.clone(), 0, 0, 1);
        emit!(d1.clone(), d2.clone(), 0, 0, 4);
    }

    // ---- Fill remaining with random sizes and mutations ----
    while count < goal {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 200),
            3 => rng.gen_range_usize(200, 2000),
            _ => rng.gen_range_usize(2, 100),
        };
        let max_d = std::cmp::max(1, std::cmp::min(200, (i32::MAX as i64 / n as i64) as i32));
        let d1 = random_deltas(&mut rng, n - 1, max_d);
        let d2 = random_deltas(&mut rng, n - 1, max_d);
        let sum1 = delta_sum(&d1);
        let sum2 = delta_sum(&d2);
        let max_base1 = std::cmp::min(200_000i64, i32::MAX as i64 - sum1);
        let max_base2 = std::cmp::min(200_000i64, i32::MAX as i64 - sum2);
        if max_base1 < 0 || max_base2 < 0 { continue; }
        let b1 = rng.gen_range_i64(0, max_base1) as i32;
        let b2 = rng.gen_range_i64(0, max_base2) as i32;
        let mk = rng.gen_range_i64(0, 5) as u8;
        emit!(d1, d2, b1, b2, mk);
    }
}
