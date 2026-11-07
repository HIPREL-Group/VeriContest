use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_non_min_or_max(nums: Vec<i32>) -> (res: i32) 
        requires 
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures 
            nums.len() < 3 ==> res == -1,
            nums.len() >= 3 ==> {
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] == res
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] < res
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] > res
            },
    {
        
    }
}

}