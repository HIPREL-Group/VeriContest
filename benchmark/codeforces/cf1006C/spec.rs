use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
        recommends 0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 { 0 }
        else { Self::prefix_sum(nums, end - 1) + nums[end - 1] as int }
    }

    pub open spec fn total_sum(nums: Seq<i64>) -> int {
        Self::prefix_sum(nums, nums.len() as int)
    }

    pub open spec fn valid_split(nums: Seq<i64>, a: int, j: int) -> bool {
        &&& 0 <= a <= j <= nums.len()
        &&& Self::prefix_sum(nums, a) == Self::total_sum(nums) - Self::prefix_sum(nums, j)
    }

    pub fn max_equal_outer_sum(nums: Vec<i64>) -> (result: i64)
        requires
            1 <= nums.len() <= 200_000,
            forall|k: int| 0 <= k < nums.len()
                ==> 1 <= #[trigger] nums[k] as int && (nums[k] as int) <= 1_000_000_000,
            Self::total_sum(nums@) <= i64::MAX,
        ensures
            forall|a: int, j: int|
                Self::valid_split(nums@, a, j)
                    ==> Self::prefix_sum(nums@, a) <= result as int,
            exists|a: int, j: int|
                Self::valid_split(nums@, a, j)
                    && Self::prefix_sum(nums@, a) == result as int,
    {
    }
}

}
