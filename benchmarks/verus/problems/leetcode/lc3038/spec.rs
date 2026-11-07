use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;


pub open spec fn spec_max_ops(nums: Seq<i32>, target: int, k: int) -> int
    decreases (nums.len() as int) - 2 * k,
{
    if 2 * k + 1 >= nums.len() {
        0
    } else if (nums[2 * k] as int) + (nums[2 * k + 1] as int) == target {
        1 + spec_max_ops(nums, target, k + 1)
    } else {
        0
    }
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> (count: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            count as int == spec_max_ops(nums@, nums[0] as int + nums[1] as int, 0),
            count >= 1,
            
            forall |k: int| 0 <= k < count
                ==> (#[trigger] nums[2 * k] as int) + (nums[2 * k + 1] as int) == nums[0] as int + nums[1] as int,
    {
    }
}

} 
