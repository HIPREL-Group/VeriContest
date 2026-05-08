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
    }

    pub fn sum_digit_differences(nums: Vec<i32>) -> (result: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000,
        ensures
            Self::sum_digit_differences_spec(nums@, result as int),
    {
    }
}

}
