use vstd::prelude::*;

verus! {

proof fn count_prefix_append(nums: Seq<i32>, v: i32, bound: int, end: int)
    requires 0 <= end <= nums.len(),
    ensures suffix_len_at_most(nums.push(v), bound, end) == suffix_len_at_most(nums, bound, end),
        count_at_most(nums.push(v), bound, end) == count_at_most(nums, bound, end),
    decreases end,
{
    if end > 0 { count_prefix_append(nums, v, bound, end - 1); }
}
pub fn generate_test_case(raw: Vec<i32>, left: i32, right: i32) -> (result: (Vec<i32>, i32, i32))
    ensures 1 <= result.0.len() <= 100000, 0 <= result.1 <= result.2 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000000000,
        count_bounded_max(result.0@, result.1 as int, result.2 as int, result.0.len() as int) <= i32::MAX,
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let left = if left < 0 { 0 } else if left > 1000000000 { 1000000000 } else { left };
    let right = if right < left { left } else if right > 1000000000 { 1000000000 } else { right };
    let mut nums: Vec<i32> = Vec::new();
    let mut lower_run = 0i64;
    let mut upper_run = 0i64;
    let mut lower_total = 0i64;
    let mut upper_total = 0i64;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 100000, nums.len() == i, 0 <= left <= right <= 1000000000,
            0 <= lower_run <= upper_run <= i,
            0 <= lower_total <= upper_total <= 100000 * i,
            upper_total - lower_total <= 2147483647,
            lower_run == suffix_len_at_most(nums@, left - 1, i as int),
            upper_run == suffix_len_at_most(nums@, right as int, i as int),
            lower_total == count_at_most(nums@, left - 1, i as int),
            upper_total == count_at_most(nums@, right as int, i as int),
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] nums[j] <= 1000000000,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 0 };
        let v = if v < 0 { 0 } else if v > 1000000000 { 1000000000 } else { v };
        let next_lower = if v < left { lower_run + 1 } else { 0 };
        let next_upper = if v <= right { upper_run + 1 } else { 0 };
        if upper_total + next_upper - lower_total - next_lower > 2147483647 {
            assert(i > 0);
            return (nums, left, right);
        }
        proof {
            count_prefix_append(nums@, v, left - 1, i as int);
            count_prefix_append(nums@, v, right as int, i as int);
        }
        nums.push(v);
        lower_run = next_lower; upper_run = next_upper;
        lower_total += next_lower; upper_total += next_upper;
        i += 1;
    }
    (nums, left, right)
}


// Spec fns copied from spec.rs (standalone, without impl Solution)

pub open spec fn suffix_len_at_most(nums: Seq<i32>, bound: int, n: int) -> int
    recommends
        0 <= n <= nums.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else if nums[n - 1] as int <= bound {
        suffix_len_at_most(nums, bound, n - 1) + 1
    } else {
        0
    }
}

pub open spec fn count_at_most(nums: Seq<i32>, bound: int, n: int) -> int
    recommends
        0 <= n <= nums.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_at_most(nums, bound, n - 1)
            + suffix_len_at_most(nums, bound, n)
    }
}

pub open spec fn count_bounded_max(nums: Seq<i32>, left: int, right: int, n: int) -> int
    recommends
        0 <= n <= nums.len(),
        left <= right,
{
    count_at_most(nums, right, n) - count_at_most(nums, left - 1, n)
}

// --- Proof lemmas for bounding count_bounded_max ---

proof fn lemma_suffix_nonneg(nums: Seq<i32>, bound: int, n: int)
    requires
        0 <= n <= nums.len(),
    ensures
        suffix_len_at_most(nums, bound, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_suffix_nonneg(nums, bound, n - 1);
    }
}

proof fn lemma_suffix_bound(nums: Seq<i32>, bound: int, n: int)
    requires
        0 <= n <= nums.len(),
    ensures
        suffix_len_at_most(nums, bound, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_suffix_bound(nums, bound, n - 1);
    }
}

proof fn lemma_count_nonneg(nums: Seq<i32>, bound: int, n: int)
    requires
        0 <= n <= nums.len(),
    ensures
        count_at_most(nums, bound, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_count_nonneg(nums, bound, n - 1);
        lemma_suffix_nonneg(nums, bound, n);
    }
}

proof fn lemma_count_bound(nums: Seq<i32>, bound: int, n: int)
    requires
        0 <= n <= nums.len(),
        n <= 46340,
    ensures
        count_at_most(nums, bound, n) <= n * n,
    decreases n,
{
    if n > 0 {
        lemma_count_bound(nums, bound, n - 1);
        lemma_suffix_bound(nums, bound, n);
        assert((n - 1) * (n - 1) == n * n - 2 * n + 1) by (nonlinear_arith);
        assert(n * n - 2 * n + 1 + n == n * n - n + 1);
    }
}

pub fn generate_candidate(
    elems: &Vec<i32>,
    left: i32,
    right: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= elems.len() <= 46340,
        forall|i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
        0 <= left <= right <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        0 <= result.1 <= result.2 <= 1_000_000_000,
        count_bounded_max(result.0@, result.1 as int, result.2 as int, result.0.len() as int) <= i32::MAX,
{
    // Copy elems into nums
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < elems.len()
        invariant
            0 <= idx <= elems.len(),
            nums.len() == idx,
            forall|k: int| 0 <= k < idx as int ==> #[trigger] nums[k] == elems[k],
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
        decreases elems.len() - idx,
    {
        nums.push(elems[idx]);
        idx = idx + 1;
    }

    // Apply mutations
    if mutation_kind == 1 {
        nums.set(0, left);
    } else if mutation_kind == 2 {
        nums.set(0, right);
    } else if mutation_kind == 3 {
        nums.set(0, 0);
    } else if mutation_kind == 4 && nums[0] < 1_000_000_000 {
        nums.set(0, (nums[0] + 1) as i32);
    } else if mutation_kind == 5 && nums[0] > 0 {
        nums.set(0, (nums[0] - 1) as i32);
    } else if mutation_kind == 6 {
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                nums.len() == elems.len(),
                forall|k: int| 0 <= k < j as int ==> #[trigger] nums[k] == left,
                forall|k: int| j as int <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
                0 <= left <= 1_000_000_000,
            decreases nums.len() - j,
        {
            nums.set(j, left);
            j = j + 1;
        }
    } else if mutation_kind == 7 {
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                nums.len() == elems.len(),
                forall|k: int| 0 <= k < j as int ==> #[trigger] nums[k] == right,
                forall|k: int| j as int <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
                0 <= right <= 1_000_000_000,
            decreases nums.len() - j,
        {
            nums.set(j, right);
            j = j + 1;
        }
    }

    proof {
        let n = nums.len() as int;
        assert(1 <= n <= 46340);
        lemma_count_nonneg(nums@, left as int - 1, n);
        lemma_count_bound(nums@, right as int, n);
        assert(count_bounded_max(nums@, left as int, right as int, n)
            <= count_at_most(nums@, right as int, n));
        assert(count_at_most(nums@, right as int, n) <= n * n);
        assert(n * n <= 46340 * 46340) by (nonlinear_arith)
            requires 0 <= n <= 46340,
        ;
        assert(46340int * 46340int <= i32::MAX as int);
    }

    (nums, left, right)
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($elems:expr, $left:expr, $right:expr, $mk:expr) => {
            if count < count_goal {
                let elems_val: Vec<i32> = $elems;
                let left_val: i32 = $left;
                let right_val: i32 = $right;
                let mk_val: u8 = $mk;
                let (nums_out, left_out, right_out) = generate_candidate(
                    &elems_val, left_val, right_val, mk_val,
                );
                let (nums_out, left_out, right_out) = generate_test_case(nums_out, left_out, right_out);
                let result = Solution::num_subarray_bounded_max(
                    nums_out.clone(), left_out, right_out,
                );
                let line = json!({
                    "input": {"nums": nums_out, "left": left_out, "right": right_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- Examples from description.md ----
    emit!(vec![2, 1, 4, 3], 2, 3, 0);
    emit!(vec![2, 9, 2, 5, 6], 2, 8, 0);

    // ---- Boundary and special cases ----
    emit!(vec![0], 0, 0, 0);
    emit!(vec![0], 0, 1_000_000_000, 0);
    emit!(vec![1_000_000_000], 0, 1_000_000_000, 0);
    emit!(vec![5], 5, 5, 0);
    emit!(vec![5], 6, 10, 0);
    emit!(vec![3, 3, 3, 3], 3, 3, 0);
    emit!(vec![3, 3, 3, 3], 0, 2, 0);
    emit!(vec![3, 3, 3, 3], 4, 10, 0);
    emit!(vec![1, 2], 1, 2, 0);
    emit!(vec![1, 2], 2, 2, 0);

    // Apply mutations to examples
    for mk in 1u8..=7 {
        emit!(vec![2, 1, 4, 3], 2, 3, mk);
        emit!(vec![2, 9, 2, 5, 6], 2, 8, mk);
    }

    // ---- Random test cases with diverse sizes ----
    while count < count_goal {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 46340),
        };

        let val_hi: i64 = match count % 4 {
            0 => 10,
            1 => 1000,
            2 => 1_000_000,
            _ => 1_000_000_000,
        };

        let mut elems = Vec::new();
        for _ in 0..n {
            let v = rng.gen_range_i64(0, val_hi) as i32;
            elems.push(v);
        }

        let a = rng.gen_range_i64(0, val_hi) as i32;
        let b = rng.gen_range_i64(0, val_hi) as i32;
        let (left, right) = if a <= b { (a, b) } else { (b, a) };

        let (left, right) = if count % 5 == 0 {
            (0i32, val_hi as i32)
        } else {
            (left, right)
        };

        let mk = rng.gen_u8() % 8;
        emit!(elems, left, right, mk);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
