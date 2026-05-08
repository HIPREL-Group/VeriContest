use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn search_insert(nums: Vec<i32>, target: i32) -> (res: i32) 
        requires 
            1 <= nums.len() <= 10_000, 
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j], 
            -10_000 <= target <= 10_000,
        ensures 
            0 <= res <= nums.len(),
            (nums[res as int] == target)
            || (target > nums[nums.len() - 1] && res == nums.len())
            || (target < nums[0] && res == 0)
            || (nums[res - 1] < target < nums[res as int]),  
    {
        
    }
}

}
