use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub fn search(nums: Vec<i32>, target: i32) -> (res: i32) 
        requires
            1 <= nums.len() <= 10_000,
            -10_000 < target < 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 < #[trigger] nums[i] < 10_000,
            forall|i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] < nums[j],
        ensures
            res < nums.len(),
            target == nums[res as int] || res == -1,
    {
        
    }

}

}
