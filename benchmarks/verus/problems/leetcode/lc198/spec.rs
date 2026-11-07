use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rob_spec(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
        decreases i,
    {
        if i <= 0 {
            nums[0] as int
        } else if i == 1 {
            if nums[0] as int > nums[1] as int { nums[0] as int } else { nums[1] as int }
        } else {
            let skip = Self::rob_spec(nums, i - 1);
            let take = Self::rob_spec(nums, i - 2) + nums[i] as int;
            if take > skip { take } else { skip }
        }
    }

    pub fn rob(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 400,
        ensures
            result == Self::rob_spec(nums@, (nums.len() - 1) as int),
    {
    }
}

} 
