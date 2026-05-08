use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_sum(nums, k - 1) + nums[k - 1] as int
    }
}

pub open spec fn spec_count_partitions(nums: Seq<i32>, n: int) -> int {
    if spec_sum(nums, n) % 2 == 0 {
        n - 1
    } else {
        0
    }
}

impl Solution {
    pub fn count_partitions(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == spec_count_partitions(nums@, nums.len() as int),
    {
    }
}

} 
