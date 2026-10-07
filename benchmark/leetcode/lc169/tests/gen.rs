use vstd::prelude::*;

verus! {

/// Copied from spec.rs (standalone version of Solution::count_occurrences).
pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occurrences(s.drop_last(), value) +
            if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

proof fn lemma_count_push_same(s: Seq<i32>, value: i32)
    ensures count_occurrences(s.push(value), value) == count_occurrences(s, value) + 1
{
    assert(s.push(value).drop_last() =~= s);
}

proof fn lemma_count_push_diff(s: Seq<i32>, v: i32, value: i32)
    requires v != value
    ensures count_occurrences(s.push(v), value) == count_occurrences(s, value)
{
    assert(s.push(v).drop_last() =~= s);
}

pub fn generate_test_case(
    majority_val: i32,
    filler_val: i32,
    fill_count: u32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        -1_000_000_000 <= majority_val <= 1_000_000_000,
        -1_000_000_000 <= filler_val <= 1_000_000_000,
        majority_val != filler_val,
        0 <= fill_count <= 24_999,
    ensures
        1 <= nums.len() <= 50_000,
        forall |i: int| 0 <= i < nums.len()
            ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        exists |i: int| 0 <= i < nums.len() &&
            #[trigger] count_occurrences(nums@, nums[i]) > nums.len() / 2,
{
    if mutation_kind == 1 {
        let n: u32 = if fill_count == 0 { 1u32 } else { 2 * fill_count + 1 };
        let mut nums: Vec<i32> = Vec::new();
        let mut idx: u32 = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                1 <= n <= 49_999,
                nums.len() == idx as int,
                -1_000_000_000 <= majority_val <= 1_000_000_000,
                count_occurrences(nums@, majority_val) == idx as nat,
                forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == majority_val,
            decreases n - idx,
        {
            proof { lemma_count_push_same(nums@, majority_val); }
            nums.push(majority_val);
            idx = idx + 1;
        }
        proof {
            assert(nums[0int] == majority_val);
            assert(count_occurrences(nums@, nums[0int]) == n as nat);
            assert(n as int > (n as int) / 2);
        }
        nums
    } else if mutation_kind == 2 {
        let mut nums: Vec<i32> = Vec::new();
        proof { lemma_count_push_same(nums@, majority_val); }
        nums.push(majority_val);
        proof {
            assert(nums[0int] == majority_val);
            assert(count_occurrences(nums@, nums[0int]) == 1nat);
            assert(nums.len() / 2 == 0int);
        }
        nums
    } else if mutation_kind == 3 && fill_count >= 1 {
        let maj_count: u32 = fill_count + 2;
        let fil_count: u32 = fill_count - 1;
        let mut nums: Vec<i32> = Vec::new();
        let mut idx: u32 = 0;
        while idx < maj_count
            invariant
                0 <= idx <= maj_count,
                maj_count == fill_count + 2,
                fil_count == fill_count - 1,
                fill_count <= 24_999, fill_count >= 1,
                nums.len() == idx as int,
                -1_000_000_000 <= majority_val <= 1_000_000_000,
                count_occurrences(nums@, majority_val) == idx as nat,
                forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == majority_val,
            decreases maj_count - idx,
        {
            proof { lemma_count_push_same(nums@, majority_val); }
            nums.push(majority_val);
            idx = idx + 1;
        }
        let mut j: u32 = 0;
        while j < fil_count
            invariant
                0 <= j <= fil_count,
                fil_count == fill_count - 1,
                fill_count <= 24_999, fill_count >= 1,
                maj_count == fill_count + 2,
                nums.len() == (maj_count + j) as int,
                -1_000_000_000 <= majority_val <= 1_000_000_000,
                -1_000_000_000 <= filler_val <= 1_000_000_000,
                majority_val != filler_val,
                count_occurrences(nums@, majority_val) == maj_count as nat,
                forall |k: int| 0 <= k < maj_count as int ==> #[trigger] nums[k] == majority_val,
                forall |k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
            decreases fil_count - j,
        {
            proof { lemma_count_push_diff(nums@, filler_val, majority_val); }
            nums.push(filler_val);
            j = j + 1;
        }
        proof {
            assert(nums[0int] == majority_val);
            assert(count_occurrences(nums@, nums[0int]) == maj_count as nat);
            assert(nums.len() == (2 * fill_count + 1) as int);
            assert(maj_count as int > nums.len() as int / 2);
        }
        nums
    } else {
        let maj_count: u32 = fill_count + 1;
        let mut nums: Vec<i32> = Vec::new();
        let mut idx: u32 = 0;
        while idx < maj_count
            invariant
                0 <= idx <= maj_count,
                maj_count == fill_count + 1,
                fill_count <= 24_999,
                nums.len() == idx as int,
                -1_000_000_000 <= majority_val <= 1_000_000_000,
                count_occurrences(nums@, majority_val) == idx as nat,
                forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == majority_val,
            decreases maj_count - idx,
        {
            proof { lemma_count_push_same(nums@, majority_val); }
            nums.push(majority_val);
            idx = idx + 1;
        }
        let mut j: u32 = 0;
        while j < fill_count
            invariant
                0 <= j <= fill_count,
                fill_count <= 24_999,
                maj_count == fill_count + 1,
                nums.len() == (maj_count + j) as int,
                -1_000_000_000 <= majority_val <= 1_000_000_000,
                -1_000_000_000 <= filler_val <= 1_000_000_000,
                majority_val != filler_val,
                count_occurrences(nums@, majority_val) == maj_count as nat,
                forall |k: int| 0 <= k < maj_count as int ==> #[trigger] nums[k] == majority_val,
                forall |k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
            decreases fill_count - j,
        {
            proof { lemma_count_push_diff(nums@, filler_val, majority_val); }
            nums.push(filler_val);
            j = j + 1;
        }
        proof {
            assert(nums[0int] == majority_val);
            assert(count_occurrences(nums@, nums[0int]) == maj_count as nat);
            assert(nums.len() == (2 * fill_count + 1) as int);
            assert(maj_count as int > nums.len() as int / 2);
        }
        nums
    }
}

} // verus!

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(169);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;
    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::majority_element(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };
    emit(vec![3, 2, 3], &mut seen, &mut out, &mut emitted);
    emit(vec![2, 2, 1, 1, 1, 2, 2], &mut seen, &mut out, &mut emitted);
    emit(vec![1], &mut seen, &mut out, &mut emitted);
    emit(vec![0, 0, 0], &mut seen, &mut out, &mut emitted);
    emit(vec![-1, -1, 5], &mut seen, &mut out, &mut emitted);
    emit(vec![1_000_000_000, 1_000_000_000, -1_000_000_000], &mut seen, &mut out, &mut emitted);
    let size_classes: Vec<(usize, usize)> = vec![
        (0, 0), (1, 4), (5, 49), (50, 499), (500, 4999), (5000, 24999),
    ];
    let boundary_vals: Vec<i32> = vec![
        0, 1, -1, 1_000_000_000, -1_000_000_000, 999_999_999, -999_999_999, 500_000_000, -500_000_000,
    ];
    let num_mutations: u8 = 4;
    for &maj in &boundary_vals {
        for mk in 0..num_mutations {
            if emitted >= count { break; }
            let fil: i32 = if maj == 0 { 1 } else { 0 };
            let ci = rng.gen_range_usize(0, size_classes.len() - 1);
            let (lo, hi) = size_classes[ci];
            let fc = rng.gen_range_usize(lo, hi) as u32;
            let nums = generate_test_case(maj, fil, fc, mk);
            emit(nums, &mut seen, &mut out, &mut emitted);
        }
    }
    while emitted < count {
        let ci = rng.gen_range_usize(0, size_classes.len() - 1);
        let (lo, hi) = size_classes[ci];
        let fc = rng.gen_range_usize(lo, hi) as u32;
        let maj = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let mut fil = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        if fil == maj { fil = if maj < 1_000_000_000 { maj + 1 } else { maj - 1 }; }
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let nums = generate_test_case(maj, fil, fc, mk);
        emit(nums, &mut seen, &mut out, &mut emitted);
    }
    eprintln!("Generated {} test cases", emitted);
}
