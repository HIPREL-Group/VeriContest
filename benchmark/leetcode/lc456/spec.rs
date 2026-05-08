use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find132pattern(nums: Vec<i32>) -> (res: bool) 
        requires 
            1 <= nums.len() <= 20_000, 
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000, 
        ensures
            res == (exists |i: int, j: int, k: int| 
                0 <= i < j < k < nums.len() &&
                #[trigger] nums[i] < #[trigger] nums[k] < #[trigger] nums[j]), 
    {
      
    }
}

}