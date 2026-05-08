use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn contains_duplicate(nums: Vec<i32>) -> (res: bool) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 1 <= i < nums.len() ==> 
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures 
            res == (exists |i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j]),
    {
        
    }
}

}