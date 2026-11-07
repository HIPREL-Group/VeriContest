use vstd::prelude::*;

verus! {

pub struct Solution;

// ── spec fn helpers (copied from spec.rs) ───────────────────────────

pub open spec fn spec_segment_sum(nums: Seq<i32>, l: int, r: int) -> int
    recommends
        0 <= l <= r <= nums.len(),
    decreases r - l,
{
    if r <= l {
        0
    } else {
        spec_segment_sum(nums, l, r - 1) + nums[r - 1] as int
    }
}

pub open spec fn spec_count_for_start(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int) -> int
    recommends
        0 <= i < nums.len(),
        i <= end_excl <= nums.len(),
    decreases end_excl - i,
{
    if end_excl <= i {
        0
    } else {
        spec_count_for_start(nums, lower, upper, i, end_excl - 1)
            + if lower <= spec_segment_sum(nums, i, end_excl) <= upper {
                1int
            } else {
                0int
            }
    }
}

pub open spec fn spec_count_starts_prefix(nums: Seq<i32>, lower: int, upper: int, upto_i: int) -> int
    recommends
        0 <= upto_i <= nums.len(),
    decreases upto_i,
{
    if upto_i <= 0 {
        0
    } else {
        spec_count_starts_prefix(nums, lower, upper, upto_i - 1)
            + spec_count_for_start(nums, lower, upper, upto_i - 1, nums.len() as int)
    }
}

pub open spec fn spec_count_range_sum(nums: Seq<i32>, lower: int, upper: int) -> int
    recommends
        1 <= nums.len(),
{
    spec_count_starts_prefix(nums, lower, upper, nums.len() as int)
}

// ── proof lemmas ────────────────────────────────────────────────────

proof fn lemma_count_for_start_bound(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int)
    requires
        0 <= i,
        i <= end_excl,
        end_excl <= nums.len(),
    ensures
        0 <= spec_count_for_start(nums, lower, upper, i, end_excl) <= end_excl - i,
    decreases end_excl - i,
{
    if end_excl > i {
        lemma_count_for_start_bound(nums, lower, upper, i, end_excl - 1);
    }
}

proof fn lemma_prefix_bound(nums: Seq<i32>, lower: int, upper: int, upto_i: int)
    requires
        0 <= upto_i,
        upto_i <= nums.len(),
    ensures
        0 <= spec_count_starts_prefix(nums, lower, upper, upto_i) <= upto_i * nums.len(),
    decreases upto_i,
{
    if upto_i > 0 {
        lemma_prefix_bound(nums, lower, upper, upto_i - 1);
        lemma_count_for_start_bound(nums, lower, upper, upto_i - 1, nums.len() as int);
        assert(spec_count_starts_prefix(nums, lower, upper, upto_i)
            == spec_count_starts_prefix(nums, lower, upper, upto_i - 1)
                + spec_count_for_start(nums, lower, upper, upto_i - 1, nums.len() as int));
        assert(spec_count_for_start(nums, lower, upper, upto_i - 1, nums.len() as int)
            <= nums.len() - (upto_i - 1));
        let n = nums.len() as int;
        let k = upto_i;
        assert(spec_count_starts_prefix(nums, lower, upper, k)
            <= (k - 1) * n + (n - (k - 1)));
        assert((k - 1) * n + (n - (k - 1)) == k * n - k + 1) by (nonlinear_arith)
            requires k >= 1, n >= 1,
        ;
        assert(k * n - k + 1 <= k * n) by (nonlinear_arith)
            requires k >= 1,
        ;
    }
}

proof fn lemma_count_range_sum_bound(nums: Seq<i32>, lower: int, upper: int)
    requires
        1 <= nums.len(),
    ensures
        0 <= spec_count_range_sum(nums, lower, upper) <= (nums.len() * nums.len()),
{
    lemma_prefix_bound(nums, lower, upper, nums.len() as int);
}

// ── generator ───────────────────────────────────────────────────────

/// Constructs valid (nums, lower, upper) inputs for count_range_sum.
///
/// Construction parameters:
///   elems  — raw array elements (length limited to 46340 so n*n <= i32::MAX)
///   lower  — lower bound of the range
///   upper  — upper bound of the range
///   mutation_kind — selects a verified mutation strategy
///
/// Mutations:
///   0 — identity
///   1 — set all elements to 0
///   2 — set first element to i32::MAX
///   3 — set first element to i32::MIN
///   4 — nudge first element up (+1 if possible)
///   5 — nudge first element down (-1 if possible)
///   6 — swap first and last elements
///   7 — set last element to 0
pub fn generate_test_case(
    elems: Vec<i32>,
    lower: i32,
    upper: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= elems.len() <= 46340,
        forall|i: int| 0 <= i < elems.len() ==> -2147483648 <= #[trigger] elems[i] <= 2147483647,
        -100000 <= lower as int <= upper as int <= 100000,
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> -2147483648 <= #[trigger] result.0[i] <= 2147483647,
        -100000 <= result.1 as int <= result.2 as int <= 100000,
        spec_count_range_sum(result.0@, result.1 as int, result.2 as int) <= i32::MAX,
{
    let n = elems.len();

    let nums: Vec<i32> = if mutation_kind == 1 {
        // set all elements to 0
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 46340,
                out.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 0i32,
                forall|j: int| 0 <= j < k ==> -2147483648 <= #[trigger] out[j] <= 2147483647,
            decreases n - k,
        {
            out.push(0i32);
            k = k + 1;
        }
        out
    } else if mutation_kind == 2 {
        // set first element to i32::MAX
        let mut out = elems;
        out.set(0, i32::MAX);
        out
    } else if mutation_kind == 3 {
        // set first element to i32::MIN
        let mut out = elems;
        out.set(0, i32::MIN);
        out
    } else if mutation_kind == 4 && elems[0] < i32::MAX {
        // nudge first element up
        let val = elems[0] + 1;
        let mut out = elems;
        out.set(0, val);
        out
    } else if mutation_kind == 5 && elems[0] > i32::MIN {
        // nudge first element down
        let val = elems[0] - 1;
        let mut out = elems;
        out.set(0, val);
        out
    } else if mutation_kind == 6 && n > 1 {
        // swap first and last elements
        let mut out = elems;
        let first = out[0];
        let last = out[n - 1];
        out.set(0, last);
        out.set(n - 1, first);
        out
    } else if mutation_kind == 7 {
        // set last element to 0
        let mut out = elems;
        out.set(n - 1, 0i32);
        out
    } else {
        // identity
        elems
    };

    proof {
        lemma_count_range_sum_bound(nums@, lower as int, upper as int);
        assert(nums.len() <= 46340);
        assert(nums.len() * nums.len() <= 46340 * 46340) by (nonlinear_arith)
            requires nums.len() <= 46340,
        ;
        assert(46340 * 46340 <= 2_147_395_600int);
        assert(2_147_395_600int <= i32::MAX as int);
    }

    (nums, lower, upper)
}

} // verus!

// ── runtime (unverified) ────────────────────────────────────────────

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

include!("../code.rs");

fn random_elems(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-2_147_483_648, 2_147_483_647) as i32);
    }
    v
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
    let mut n_emitted = 0usize;

    let mut emit = |nums: Vec<i32>, lower: i32, upper: i32,
                     seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                     n_emitted: &mut usize| {
        if *n_emitted >= count { return; }
        let key = format!("{:?}|{}|{}", nums, lower, upper);
        if !seen.insert(key) { return; }
        let result = Solution::count_range_sum(nums.clone(), lower, upper);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "lower": lower, "upper": upper},
            "output": result
        })).unwrap();
        *n_emitted += 1;
    };

    // ── Example inputs from description.md ──
    {
        let (nums, lower, upper) = generate_test_case(vec![-2, 5, -1], -2, 2, 0);
        emit(nums, lower, upper, &mut seen, &mut out, &mut n_emitted);
    }
    {
        let (nums, lower, upper) = generate_test_case(vec![0], 0, 0, 0);
        emit(nums, lower, upper, &mut seen, &mut out, &mut n_emitted);
    }

    // ── Curated seed inputs x all mutations ──
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![-1],
        vec![i32::MAX],
        vec![i32::MIN],
        vec![0, 0],
        vec![1, -1],
        vec![-100000, 100000],
        vec![1, 2, 3, 4, 5],
        vec![-5, -4, -3, -2, -1],
        vec![0, 0, 0, 0, 0],
        vec![100, -100, 100, -100],
    ];
    let lower_uppers: Vec<(i32, i32)> = vec![
        (-2, 2),
        (0, 0),
        (-100000, 100000),
        (1, 1),
        (-1, -1),
        (0, 100000),
        (-100000, 0),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    for sa in &seed_arrays {
        for &(lo, hi) in &lower_uppers {
            for &mk in &mutation_kinds {
                if n_emitted >= count { break; }
                let (nums, lower, upper) = generate_test_case(sa.clone(), lo, hi, mk);
                emit(nums, lower, upper, &mut seen, &mut out, &mut n_emitted);
            }
        }
    }

    // ── Random inputs with size classes ──
    while n_emitted < count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 46340),   // max
        };

        let elems = random_elems(&mut rng, n);

        let (lo, hi) = if rng.gen_range_usize(0, 4) == 0 {
            let choices: Vec<(i32, i32)> = vec![
                (-100000, 100000), (0, 0), (-100000, -100000), (100000, 100000),
                (-1, 1), (0, 100000), (-100000, 0),
            ];
            let idx = rng.gen_range_usize(0, choices.len() - 1);
            choices[idx]
        } else {
            let l = rng.gen_range_i64(-100000, 100000) as i32;
            let u = rng.gen_range_i64(l as i64, 100000) as i32;
            (l, u)
        };

        let mk = rng.gen_range_usize(0, 7) as u8;
        let (nums, lower, upper) = generate_test_case(elems, lo, hi, mk);
        emit(nums, lower, upper, &mut seen, &mut out, &mut n_emitted);
    }
}
