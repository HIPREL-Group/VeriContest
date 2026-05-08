use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(nums, k - 1) + nums[k - 1] as int
    }
}

pub open spec fn spec_boundary_count(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if spec_prefix_sum(nums, k) == 0 {
        spec_boundary_count(nums, k - 1) + 1
    } else {
        spec_boundary_count(nums, k - 1)
    }
}

impl Solution {
    pub fn return_to_boundary_count(nums: Vec<i32>) -> (count: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != 0,
        ensures
            count == spec_boundary_count(nums@, nums.len() as int),
    {
    }
}

} 
