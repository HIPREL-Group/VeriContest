use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn odd_sum_before(nums: Seq<i64>, end_pos: int) -> int
        recommends
            0 <= end_pos <= nums.len(),
        decreases end_pos,
    {
        if end_pos <= 0 {
            0
        } else {
            Self::odd_sum_before(nums, end_pos - 1) + if end_pos % 2 == 1 {
                nums[end_pos - 1] as int
            } else {
                0
            }
        }
    }

    pub open spec fn even_sum_before(nums: Seq<i64>, end_pos: int) -> int
        recommends
            0 <= end_pos <= nums.len(),
        decreases end_pos,
    {
        if end_pos <= 0 {
            0
        } else {
            Self::even_sum_before(nums, end_pos - 1) + if end_pos % 2 == 0 {
                nums[end_pos - 1] as int
            } else {
                0
            }
        }
    }

    pub open spec fn odd_sum_after(nums: Seq<i64>, start_idx: int) -> int
        recommends
            0 <= start_idx <= nums.len(),
        decreases nums.len() as int - start_idx,
    {
        if start_idx >= nums.len() as int {
            0
        } else {
            let new_pos = start_idx;
            (if new_pos % 2 == 1 { nums[start_idx] as int } else { 0 })
                + Self::odd_sum_after(nums, start_idx + 1)
        }
    }

    pub open spec fn even_sum_after(nums: Seq<i64>, start_idx: int) -> int
        recommends
            0 <= start_idx <= nums.len(),
        decreases nums.len() as int - start_idx,
    {
        if start_idx >= nums.len() as int {
            0
        } else {
            let new_pos = start_idx;
            (if new_pos % 2 == 0 { nums[start_idx] as int } else { 0 })
                + Self::even_sum_after(nums, start_idx + 1)
        }
    }

    pub open spec fn odd_day_sum_after_removal(nums: Seq<i64>, remove_pos: int) -> int
        recommends
            1 <= remove_pos <= nums.len(),
    {
        let remove_idx = remove_pos - 1;
        Self::odd_sum_before(nums, remove_idx) + Self::odd_sum_after(nums, remove_pos)
    }

    pub open spec fn even_day_sum_after_removal(nums: Seq<i64>, remove_pos: int) -> int
        recommends
            1 <= remove_pos <= nums.len(),
    {
        let remove_idx = remove_pos - 1;
        Self::even_sum_before(nums, remove_idx) + Self::even_sum_after(nums, remove_pos)
    }

    pub open spec fn is_good_candy(nums: Seq<i64>, i: int) -> bool
        recommends
            1 <= i <= nums.len(),
    {
        Self::odd_day_sum_after_removal(nums, i) == Self::even_day_sum_after_removal(nums, i)
    }

    pub open spec fn count_good_candies_upto(nums: Seq<i64>, i_end: int) -> nat
        recommends
            0 <= i_end <= nums.len(),
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            Self::count_good_candies_upto(nums, i_end - 1) + if Self::is_good_candy(nums, i_end) {
                1nat
            } else {
                0nat
            }
        }
    }

    pub open spec fn count_good_candies(nums: Seq<i64>) -> nat {
        Self::count_good_candies_upto(nums, nums.len() as int)
    }

    pub fn count_equal_sums(a: Vec<i64>) -> (result: i32)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 10_000,
        ensures
            result as int == Self::count_good_candies(a@),
    {
    }
}

}
