use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_ones(nums: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            Self::count_ones(nums, start + 1, end) + if nums[start] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn total_ones(nums: Seq<i32>) -> int {
        Self::count_ones(nums, 0, nums.len() as int)
    }

    pub open spec fn flip_value(x: i32) -> i32 {
        (1int - x as int) as i32
    }

    pub open spec fn after_flip(nums: Seq<i32>, i: int, j: int, k: int) -> i32
        recommends
            0 <= i <= j < nums.len(),
            0 <= k < nums.len(),
    {
        if i <= k && k <= j {
            Self::flip_value(nums[k])
        } else {
            nums[k]
        }
    }

    pub open spec fn count_ones_after_flip(nums: Seq<i32>, i: int, j: int, end: int) -> int
        recommends
            0 <= i <= j < nums.len(),
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_ones_after_flip(nums, i, j, end - 1) + if Self::after_flip(nums, i, j, end - 1) == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn count_ones_after_flip_window(nums: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i <= j < nums.len(),
    {
        Self::count_ones_after_flip(nums, i, j, nums.len() as int)
    }

    pub open spec fn max_ones_over_windows(nums: Seq<i32>, i: int, j_end: int) -> int
        recommends
            0 <= i <= j_end <= nums.len(),
        decreases j_end - i,
    {
        if i >= j_end {
            0
        } else {
            let current = Self::count_ones_after_flip_window(nums, i, j_end - 1);
            let rest = Self::max_ones_over_windows(nums, i, j_end - 1);
            if current > rest { current } else { rest }
        }
    }

    pub open spec fn max_ones_all_windows(nums: Seq<i32>, i_end: int) -> int
        recommends
            0 <= i_end <= nums.len(),
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            let current_row = Self::max_ones_over_windows(nums, i_end - 1, nums.len() as int);
            let rest = Self::max_ones_all_windows(nums, i_end - 1);
            if current_row > rest { current_row } else { rest }
        }
    }

    pub open spec fn max_ones_after_one_flip(nums: Seq<i32>) -> int {
        if nums.len() == 0 {
            0
        } else {
            Self::max_ones_all_windows(nums, nums.len() as int)
        }
    }

    pub fn max_ones_after_flip(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 100,
            forall |k: int| 0 <= k < a.len() ==> (#[trigger] a[k] == 0 || a[k] == 1),
        ensures
            result == Self::max_ones_after_one_flip(a@),
            forall |i: int, j: int| 0 <= i <= j < a.len() ==>
                Self::count_ones_after_flip_window(a@, i, j) <= result,
            exists |i: int, j: int| 0 <= i <= j < a.len() &&
                Self::count_ones_after_flip_window(a@, i, j) == result,
    {
    }
}

}
