use vstd::prelude::*;

verus! {

pub open spec fn get_sum(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else {
        nums[start] + get_sum(nums, start + 1, end)
    }
}

proof fn lemma_get_sum_nonneg(nums: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= nums.len(),
        forall|k: int| start <= k < end ==> nums[k] >= 0,
    ensures
        get_sum(nums, start, end) >= 0,
    decreases end - start,
{
    if start < end {
        lemma_get_sum_nonneg(nums, start + 1, end);
    }
}

proof fn lemma_get_sum_split(nums: Seq<i32>, a: int, b: int, c: int)
    requires
        0 <= a <= b <= c <= nums.len(),
    ensures
        get_sum(nums, a, c) == get_sum(nums, a, b) + get_sum(nums, b, c),
    decreases b - a,
{
    if a < b {
        lemma_get_sum_split(nums, a + 1, b, c);
    }
}

proof fn lemma_subarray_bounded(nums: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> nums[k] >= 0,
        get_sum(nums, 0, nums.len() as int) <= i32::MAX,
    ensures
        0 <= get_sum(nums, i, j) <= i32::MAX,
{
    lemma_get_sum_nonneg(nums, i, j);
    lemma_get_sum_split(nums, 0, i, nums.len() as int);
    lemma_get_sum_split(nums, i, j, nums.len() as int);
    lemma_get_sum_nonneg(nums, 0, i);
    lemma_get_sum_nonneg(nums, j, nums.len() as int);
}

proof fn lemma_get_sum_append(nums: Seq<i32>, val: i32, start: int, end: int)
    requires
        0 <= start <= end <= nums.len(),
    ensures
        get_sum(nums.push(val), start, end) == get_sum(nums, start, end),
    decreases end - start,
{
    if start < end {
        assert(nums.push(val)[start] == nums[start]);
        lemma_get_sum_append(nums, val, start + 1, end);
    }
}

proof fn lemma_get_sum_push_total(nums: Seq<i32>, val: i32)
    ensures
        get_sum(nums.push(val), 0, (nums.len() + 1) as int)
            == get_sum(nums, 0, nums.len() as int) + (val as int),
{
    let pushed = nums.push(val);
    let n = nums.len() as int;
    lemma_get_sum_append(nums, val, 0, n);
    lemma_get_sum_split(pushed, 0, n, n + 1);
    assert(pushed[n] == val);
    reveal_with_fuel(get_sum, 2);
    assert(get_sum(pushed, n, n + 1) == val as int);
}

pub fn generate_test_case(
    raw_values: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= raw_values.len() <= 100_000,
        forall|i: int| 0 <= i < raw_values@.len() ==> 0 <= #[trigger] raw_values@[i] <= 1_000_000_000,
        1 <= k <= i32::MAX,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0@.len() ==> 0 <= #[trigger] result.0@[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j <= result.0@.len() ==> 0 <= #[trigger] get_sum(result.0@, i, j) <= i32::MAX,
        1 <= result.1 <= i32::MAX,
{
    let n = raw_values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut running_sum: i64 = 0;
    let max_sum: i64 = i32::MAX as i64;

    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            n == raw_values.len(),
            1 <= n <= 100_000,
            nums.len() == idx,
            0 <= running_sum <= max_sum,
            max_sum == i32::MAX as i64,
            forall|i: int| 0 <= i < idx as int ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000,
            running_sum == get_sum(nums@, 0, idx as int),
            forall|i: int| 0 <= i < raw_values@.len() ==> 0 <= #[trigger] raw_values@[i] <= 1_000_000_000,
        decreases n - idx,
    {
        let remaining: i64 = max_sum - running_sum;
        let raw: i64 = raw_values[idx] as i64;
        let val_i64: i64 = if raw <= remaining { raw } else { remaining };

        assert(0 <= val_i64 <= 1_000_000_000);
        let val: i32 = val_i64 as i32;

        let ghost old_seq = nums@;
        nums.push(val);
        running_sum = running_sum + val as i64;

        proof {
            lemma_get_sum_push_total(old_seq, val);
            assert(nums@ =~= old_seq.push(val));
        }

        idx = idx + 1;
    }

    proof {
        assert forall|i: int, j: int|
            0 <= i < j <= nums@.len()
        implies
            0 <= #[trigger] get_sum(nums@, i, j) <= i32::MAX
        by {
            lemma_subarray_bounded(nums@, i, j);
        };
    }

    let k_out: i32 = if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        2i32
    } else if mutation_kind == 3 {
        i32::MAX
    } else if mutation_kind == 4 {
        7i32
    } else if mutation_kind == 5 {
        100i32
    } else {
        k
    };

    (nums, k_out)
}

} // verus!

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

fn gen_raw_values(rng: &mut Rng, n: usize, val_hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(0, val_hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(523);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut rng = Rng::new(seed);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}:{}", nums, k);
        if !seen.insert(key) { return; }
        let output = Solution::check_subarray_sum(nums.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![23, 2, 4, 6, 7], 6),
        (vec![23, 2, 6, 4, 7], 6),
        (vec![23, 2, 6, 4, 7], 13),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut emitted);
    }

    // Edge cases
    let edge_cases: Vec<(Vec<i32>, i32)> = vec![
        (vec![0, 0], 1),             // two zeros, always true
        (vec![0, 0], i32::MAX),      // two zeros, large k
        (vec![1, 0], 1),             // sum = 1, k = 1
        (vec![1_000_000_000, 1_000_000_000], 1), // large elements
        (vec![0], 1),                // single element
        (vec![5, 5, 5], 5),          // all same, divisible
        (vec![1, 2, 3, 4, 5], 15),   // total sum equals k
        (vec![1, 1], 2),             // pair sums to k
        (vec![0, 0, 0, 0, 0], 7),    // all zeros
    ];
    for (nums, k) in edge_cases {
        emit(nums, k, &mut seen, &mut out, &mut emitted);
    }

    // Mutation kinds for k-diversity
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Random test cases with size classes
    while emitted < count {
        let i = emitted;

        // Size class for array length
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // max
        };

        // Value range scaled to array size so budget capping is rare
        let val_hi: i64 = std::cmp::max(1, (i32::MAX as i64) / (n as i64));
        let val_hi = std::cmp::min(val_hi, 1_000_000_000);

        let raw_values = gen_raw_values(&mut rng, n, val_hi);

        // k value with boundary mixing
        let k: i32 = if i % 5 == 0 {
            *[1i32, 2, 7, 100, i32::MAX].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(1, i32::MAX as i64) as i32
        };

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (nums, k_out) = generate_test_case(raw_values, k, mk);
        emit(nums, k_out, &mut seen, &mut out, &mut emitted);
    }
}
