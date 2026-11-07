use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, end: int) -> int
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

    pub open spec fn valid_split(nums: Seq<i32>, i: int) -> bool {
        if 0 <= i < nums.len() - 1 {
            let left = Self::prefix_sum(nums, i + 1);
            left >= Self::prefix_sum(nums, nums.len() as int) - left
        } else {
            false
        }
    }

    pub open spec fn count_valid_splits(nums: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto,
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::count_valid_splits(nums, upto - 1)
                + if Self::valid_split(nums, upto - 1) { 1int } else { 0int }
        }
    }

    pub fn ways_to_split_array(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            0 <= result as int <= nums.len() as int - 1,
            result as int == Self::count_valid_splits(nums@, nums.len() as int - 1),
    {
    }
}

}
