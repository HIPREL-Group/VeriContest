use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_diff_count(a: int, b: int, pos: int) -> int
        decreases pos,
    {
        if pos <= 0 {
            0
        } else {
            Self::digit_diff_count(a / 10, b / 10, pos - 1)
                + if a % 10 != b % 10 { 1int } else { 0int }
        }
    }

    pub open spec fn pair_sum_for_i(nums: Seq<i32>, i: int, j: int) -> int
        decreases j,
    {
        if j <= 0 {
            0
        } else {
            Self::pair_sum_for_i(nums, i, j - 1)
                + Self::digit_diff_count(nums[i] as int, nums[j - 1] as int, 9)
        }
    }

    pub open spec fn all_pair_sum(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::all_pair_sum(nums, end - 1) + Self::pair_sum_for_i(nums, end - 1, end - 1)
        }
    }

    pub open spec fn sum_digit_differences_spec(nums: Seq<i32>, result: int) -> bool {
        &&& 2 <= nums.len() <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000
        &&& result == Self::all_pair_sum(nums, nums.len() as int)
    }

    proof fn lemma_digit_diff_count_bounds(a: int, b: int, pos: int)
        requires
            0 <= pos <= 9,
        ensures
            0 <= Self::digit_diff_count(a, b, pos) <= pos,
        decreases pos,
    {
        if pos > 0 {
            Self::lemma_digit_diff_count_bounds(a / 10, b / 10, pos - 1);
        }
    }

    proof fn lemma_pair_sum_for_i_bound(nums: Seq<i32>, i: int, j: int)
        requires
            0 <= j <= i < nums.len(),
        ensures
            0 <= Self::pair_sum_for_i(nums, i, j) <= 9 * j,
        decreases j,
    {
        if j > 0 {
            Self::lemma_pair_sum_for_i_bound(nums, i, j - 1);
            Self::lemma_digit_diff_count_bounds(nums[i] as int, nums[j - 1] as int, 9);
        }
    }

    proof fn lemma_all_pair_sum_bound(nums: Seq<i32>, end: int)
        requires
            0 <= end <= nums.len(),
            end <= 100000,
        ensures
            0 <= Self::all_pair_sum(nums, end),
            Self::all_pair_sum(nums, end) <= 9 * end * end,
            Self::all_pair_sum(nums, end) <= 90_000_000_000,
        decreases end,
    {
        if end > 0 {
            assert(end >= 1);
            Self::lemma_all_pair_sum_bound(nums, end - 1);
            Self::lemma_pair_sum_for_i_bound(nums, end - 1, end - 1);
            assert(Self::all_pair_sum(nums, end)
                == Self::all_pair_sum(nums, end - 1) + Self::pair_sum_for_i(nums, end - 1, end - 1));
            assert(Self::pair_sum_for_i(nums, end - 1, end - 1) <= 9 * (end - 1));
            assert(Self::all_pair_sum(nums, end - 1) <= 9 * (end - 1) * (end - 1));
            assert(Self::all_pair_sum(nums, end) <= 9 * (end - 1) * (end - 1) + 9 * (end - 1));
            assert(9 * (end - 1) * (end - 1) + 9 * (end - 1) <= 9 * end * end)
                by (nonlinear_arith)
                requires end >= 1;
            assert(Self::all_pair_sum(nums, end) <= 9 * end * end);
        }
        assert(end >= 0);
        assert(end <= 100000);
        assert(0 <= end <= 100000);
        assert(9 * end * end <= 90_000_000_000)
            by (nonlinear_arith)
            requires 0 <= end <= 100000;
        assert(Self::all_pair_sum(nums, end) <= 90_000_000_000);
    }

    fn digit_diff_count_exec(a: i32, b: i32, pos: usize) -> (res: i64)
        requires
            0 <= pos <= 9,
            0 <= a < 1_000_000_000,
            0 <= b < 1_000_000_000,
        ensures
            res as int == Self::digit_diff_count(a as int, b as int, pos as int),
            0 <= res <= pos as int,
        decreases pos,
    {
        if pos == 0 {
            0
        } else {
            let next = Self::digit_diff_count_exec(a / 10, b / 10, pos - 1);
            let add = if a % 10 != b % 10 { 1i64 } else { 0i64 };
            assert(Self::digit_diff_count(a as int, b as int, pos as int)
                == Self::digit_diff_count((a / 10) as int, (b / 10) as int, (pos - 1) as int)
                    + if (a as int) % 10 != (b as int) % 10 { 1int } else { 0int });
            assert((a / 10) as int == (a as int) / 10);
            assert((b / 10) as int == (b as int) / 10);
            assert((a % 10) as int == (a as int) % 10);
            assert((b % 10) as int == (b as int) % 10);
            next + add
        }
    }

    fn pair_sum_for_i_exec(nums: &Vec<i32>, i: usize, j: usize) -> (res: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] < 1_000_000_000,
            i < nums.len(),
            j <= i,
        ensures
            res as int == Self::pair_sum_for_i(nums@, i as int, j as int),
            0 <= res,
            res as int <= 9 * (j as int),
        decreases j,
    {
        if j == 0 {
            0
        } else {
            let prev = Self::pair_sum_for_i_exec(nums, i, j - 1);
            let diff = Self::digit_diff_count_exec(nums[i], nums[j - 1], 9);
            assert(j > 0);
            assert((j - 1) as int == j as int - 1);
            assert(prev as int <= 9 * ((j - 1) as int));
            assert(diff as int <= 9);
            assert((prev as int) + (diff as int) <= 9 * ((j - 1) as int) + 9);
            assert(9 * ((j - 1) as int) + 9 == 9 * (j as int)) by (nonlinear_arith);
            assert(j <= 100000);
            assert(j as int <= 100000);
            assert(0 <= j as int <= 100000);
            assert(9 * (j as int) <= 900000)
                by (nonlinear_arith)
                requires 0 <= j as int <= 100000;
            assert(900000int <= i64::MAX);
            assert(prev + diff <= i64::MAX);
            assert(Self::pair_sum_for_i(nums@, i as int, j as int)
                == Self::pair_sum_for_i(nums@, i as int, (j - 1) as int)
                    + Self::digit_diff_count(nums@[i as int] as int, nums@[(j - 1) as int] as int, 9));
            prev + diff
        }
    }

    fn all_pair_sum_exec(nums: &Vec<i32>, end: usize) -> (res: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] < 1_000_000_000,
            end <= nums.len(),
        ensures
            res as int == Self::all_pair_sum(nums@, end as int),
            0 <= res,
        decreases end,
    {
        if end == 0 {
            0
        } else {
            let prev = Self::all_pair_sum_exec(nums, end - 1);
            let add = Self::pair_sum_for_i_exec(nums, end - 1, end - 1);
            assert(end > 0);
            assert(end <= nums.len());
            assert(nums.len() <= 100000);
            assert(end <= 100000);
            assert((end - 1) as int <= 99999);
            proof {
                Self::lemma_all_pair_sum_bound(nums@, (end - 1) as int);
            }
            assert(prev as int <= 90_000_000_000);
            assert(add as int <= 9 * ((end - 1) as int));
            assert(end as int <= 100000);
            assert(0 <= (end - 1) as int <= 99999);
            assert(add as int <= 900000)
                by (nonlinear_arith)
                requires add as int <= 9 * ((end - 1) as int), 0 <= (end - 1) as int <= 99999;
            assert(prev >= 0);
            assert(prev as int <= i64::MAX);
            assert((prev as int) + (add as int) <= 90_000_000_000 + 900000);
            assert(90_000_000_000 + 900000 == 90_000_900_000);
            assert(90_000_900_000int <= i64::MAX);
            assert(prev + add <= i64::MAX);
            assert(Self::all_pair_sum(nums@, end as int)
                == Self::all_pair_sum(nums@, (end - 1) as int)
                    + Self::pair_sum_for_i(nums@, (end - 1) as int, (end - 1) as int));
            prev + add
        }
    }

    pub fn sum_digit_differences(nums: Vec<i32>) -> (result: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000,
        ensures
            Self::sum_digit_differences_spec(nums@, result as int),
    {
        Self::all_pair_sum_exec(&nums, nums.len())
    }
}

}
