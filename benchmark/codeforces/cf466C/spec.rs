use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn total_sum(nums: Seq<i64>) -> int {
        Self::prefix_sum(nums, nums.len() as int)
    }

    pub open spec fn valid_split_pair(nums: Seq<i64>, i: int, j: int) -> bool {
        &&& 0 <= i < j < nums.len() - 1
        &&& {
            let s1 = Self::prefix_sum(nums, i + 1);
            let s2 = Self::prefix_sum(nums, j + 1) - Self::prefix_sum(nums, i + 1);
            let s3 = Self::total_sum(nums) - Self::prefix_sum(nums, j + 1);
            s1 == s2 && s2 == s3
        }
    }

    pub open spec fn count_valid_first_cuts(nums: Seq<i64>, j: int, i_end: int) -> nat
        recommends
            -1 <= j < nums.len() - 1,
            0 <= i_end <= j,
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            Self::count_valid_first_cuts(nums, j, i_end - 1) + if Self::valid_split_pair(nums, i_end - 1, j) {
                1nat
            } else {
                0nat
            }
        }
    }

    pub open spec fn count_valid_splits_upto(nums: Seq<i64>, j_end: int) -> nat
        recommends
            0 <= j_end <= nums.len() - 1,
        decreases j_end,
    {
        if j_end <= 0 {
            0
        } else {
            Self::count_valid_splits_upto(nums, j_end - 1)
                + Self::count_valid_first_cuts(nums, j_end - 1, j_end - 1)
        }
    }

    pub open spec fn count_valid_splits(nums: Seq<i64>) -> nat {
        if nums.len() < 3 {
            0
        } else {
            Self::count_valid_splits_upto(nums, nums.len() - 1)
        }
    }

    pub fn count_equal_sum_splits(nums: Vec<i64>) -> (result: u64)
        requires
            1 <= nums.len() <= 500_000,
            forall |k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
        ensures
            result as int == Self::count_valid_splits(nums@),
    {
    }
}

}
