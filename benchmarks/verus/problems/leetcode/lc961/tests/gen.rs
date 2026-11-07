use vstd::prelude::*;

verus! {

// ── spec fn helpers (from spec.rs, Self:: removed) ──────────────────────────

pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occurrences(s.drop_last(), value) + if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

pub open spec fn valid_input(nums: Seq<i32>) -> bool {
    4 <= nums.len() <= 10_000 &&
    nums.len() % 2 == 0 &&
    exists |k: int|
        0 <= k < nums.len() &&
        (forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 10_000) &&
        count_occurrences(nums, nums[k]) == nums.len() / 2 &&
        (forall |i: int| 0 <= i < nums.len() && nums[i] != nums[k] ==> #[trigger] count_occurrences(nums, nums[i]) == 1)
}

// ── proof helpers ───────────────────────────────────────────────────────────

proof fn lemma_count_zero_if_absent(s: Seq<i32>, v: i32)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
    ensures
        count_occurrences(s, v) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_zero_if_absent(s.drop_last(), v);
    }
}

/// count of r in a seq whose first `prefix_len` elements are r and the rest are not.
proof fn lemma_count_split(s: Seq<i32>, r: i32, prefix_len: int)
    requires
        0 <= prefix_len <= s.len(),
        forall|i: int| 0 <= i < prefix_len ==> s[i] == r,
        forall|i: int| prefix_len <= i < s.len() ==> s[i] != r,
    ensures
        count_occurrences(s, r) == prefix_len as nat,
    decreases s.len(),
{
    if s.len() == 0 {
    } else if s.len() as int == prefix_len {
        assert(s.last() == r);
        assert forall|i: int| 0 <= i < prefix_len - 1 implies s.drop_last()[i] == r by {
            assert(s.drop_last()[i] == s[i]);
        };
        lemma_count_split(s.drop_last(), r, prefix_len - 1);
    } else {
        assert(s.last() != r);
        assert forall|i: int| 0 <= i < prefix_len implies s.drop_last()[i] == r by {
            assert(s.drop_last()[i] == s[i]);
        };
        assert forall|i: int| prefix_len <= i < s.drop_last().len() implies s.drop_last()[i] != r by {
            assert(s.drop_last()[i] == s[i]);
        };
        lemma_count_split(s.drop_last(), r, prefix_len);
    }
}

/// count of v in a seq where v appears exactly once (at `pos`).
proof fn lemma_count_unique(s: Seq<i32>, v: i32, pos: int)
    requires
        0 <= pos < s.len(),
        s[pos] == v,
        forall|i: int| 0 <= i < s.len() && i != pos ==> s[i] != v,
    ensures
        count_occurrences(s, v) == 1nat,
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.last() == v);
        assert(s.drop_last() =~= Seq::<i32>::empty());
        assert(count_occurrences(s.drop_last(), v) == 0nat);
    } else if pos == s.len() - 1 {
        assert(s.last() == v);
        assert forall|i: int| 0 <= i < s.drop_last().len() implies s.drop_last()[i] != v by {
            assert(s.drop_last()[i] == s[i]);
        };
        lemma_count_zero_if_absent(s.drop_last(), v);
    } else {
        assert(s.last() != v);
        assert(s.drop_last()[pos] == v) by { assert(s.drop_last()[pos] == s[pos]); };
        assert forall|i: int| 0 <= i < s.drop_last().len() && i != pos implies s.drop_last()[i] != v by {
            assert(s.drop_last()[i] == s[i]);
        };
        lemma_count_unique(s.drop_last(), v, pos);
    }
}

// ── generator ───────────────────────────────────────────────────────────────

/// Build a valid array of length 2·half_len.
///
/// Construction: [r, r, …, r, 0, 1, …, half_len-1]
///   where r ≥ half_len, so unique fillers are all < r.
///
/// mutation_kind selects the effective repeated value:
///   0 → repeated_val   (given)
///   1 → half_len       (minimum valid)
///   2 → 10 000         (maximum valid)
///   _ → repeated_val   (fallback)
pub fn generate_test_case(
    half_len: usize,
    repeated_val: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= half_len <= 5000,
        0 <= repeated_val <= 10_000,
        half_len <= repeated_val as usize,
    ensures
        valid_input(result@),
{
    let r: i32 = if mutation_kind == 1 {
        half_len as i32
    } else if mutation_kind == 2 {
        10_000i32
    } else {
        repeated_val
    };

    // ── Phase 1: push r  half_len times ─────────────────────────────────
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < half_len
        invariant
            0 <= i <= half_len,
            nums.len() == i,
            forall|idx: int| 0 <= idx < i as int ==> nums@[idx] == r,
        decreases half_len - i,
    {
        nums.push(r);
        i = i + 1;
    }

    // ── Phase 2: push unique fillers 0, 1, …, half_len-1 ───────────────
    let mut j: usize = 0;
    while j < half_len
        invariant
            0 <= j <= half_len,
            2 <= half_len <= 5000,
            0 <= r <= 10_000,
            half_len as i32 <= r,
            nums.len() == half_len + j,
            forall|idx: int| 0 <= idx < half_len as int ==> nums@[idx] == r,
            forall|idx: int| half_len as int <= idx < (half_len + j) as int
                ==> nums@[idx] == (idx - half_len as int) as i32,
        decreases half_len - j,
    {
        nums.push(j as i32);
        j = j + 1;
    }

    // ── Final proof of valid_input ──────────────────────────────────────
    proof {
        // ---- length constraints ----
        assert(nums.len() == 2 * half_len);
        assert(4 <= nums.len() <= 10_000);
        assert(nums.len() % 2 == 0);

        // ---- all elements in [0, 10 000] ----
        assert forall|i: int| 0 <= i < nums.len()
            implies 0 <= #[trigger] nums@[i] <= 10_000 by
        {
            if i < half_len as int {
                assert(nums@[i] == r);
            } else {
                assert(nums@[i] == (i - half_len as int) as i32);
            }
        };

        // ---- suffix elements ≠ r ----
        assert forall|i: int| half_len as int <= i < nums.len()
            implies nums@[i] != r by
        {
            assert(nums@[i] == (i - half_len as int) as i32);
            assert((i - half_len as int) < half_len as int);
            assert(half_len as int <= r as int);
        };

        // ---- count(r) == half_len ----
        lemma_count_split(nums@, r, half_len as int);

        // ---- each filler value appears exactly once ----
        assert forall|i: int| 0 <= i < nums.len() && nums@[i] != nums@[0]
            implies #[trigger] count_occurrences(nums@, nums@[i]) == 1nat by
        {
            assert(nums@[0] == r);
            assert(i >= half_len as int);
            let v = nums@[i];

            // v sits only at position i
            assert forall|idx: int| 0 <= idx < nums.len() && idx != i
                implies nums@[idx] != v by
            {
                if idx < half_len as int {
                    assert(nums@[idx] == r);
                    assert(v != r);
                } else {
                    assert(nums@[idx] == (idx - half_len as int) as i32);
                    assert(idx != i);
                }
            };
            lemma_count_unique(nums@, v, i);
        };

        // ---- witness for the existential (k = 0) ----
        assert(0 <= 0int < nums.len() as int);
        assert(count_occurrences(nums@, nums@[0]) == nums.len() / 2);
    }

    nums
}

} // verus!

// ── PRNG ────────────────────────────────────────────────────────────────────

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

// ── Solution (from code.rs) ─────────────────────────────────────────────────

struct Solution;
include!("../code.rs");

fn gen(half_len: usize, repeated_val: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(half_len, repeated_val, mutation_kind)
}

// ── main ────────────────────────────────────────────────────────────────────

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!())
        .parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::repeated_n_times(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // ---- examples from description.md ----
    emit(vec![1,2,3,3], &mut seen, &mut out, &mut emitted);
    emit(vec![2,1,2,5,3,2], &mut seen, &mut out, &mut emitted);
    emit(vec![5,1,5,2,5,3,5,4], &mut seen, &mut out, &mut emitted);

    // ---- systematic: size classes × mutation kinds ----
    let sizes: Vec<usize> = vec![2, 3, 5, 10, 50, 100, 500, 1000, 5000];
    let mks: Vec<u8> = vec![0, 1, 2];

    for &hl in sizes.iter() {
        for &mk in mks.iter() {
            let rv = if mk == 1 {
                hl as i32
            } else if mk == 2 {
                10_000i32
            } else {
                rng.gen_range_i64(hl as i64, 10_000) as i32
            };
            let nums = gen(hl, rv, mk);
            emit(nums, &mut seen, &mut out, &mut emitted);
        }
    }

    // ---- random test cases to fill remaining ----
    while emitted < count {
        let hl = match emitted % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let rv = rng.gen_range_i64(hl as i64, 10_000) as i32;
        let mk = rng.gen_range_usize(0, 2) as u8;
        let nums = gen(hl, rv, mk);
        emit(nums, &mut seen, &mut out, &mut emitted);
    }
}
