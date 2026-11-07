use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_duplicate(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() - 1 <= 100_000, 
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len() - 1, 
            exists |i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j],
            forall |i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < j1 < nums.len() &&
                0 <= i2 < j2 < nums.len() &&
                nums[i1] == nums[j1] &&
                nums[i2] == nums[j2] ==> nums[i1] == nums[i2],
        ensures 
            1 <= res <= nums.len() - 1,
            exists |i: int, j: int| 0 <= i < j < nums.len() && 
                nums[i] == nums[j] && nums[i] == res,
    {
        
    }
}

}