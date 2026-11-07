use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_maximum_xor(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 200_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX, 
        ensures 
            forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                ==> res >= (nums[i] ^ nums[j]),
            exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                && res == (nums[i] ^ nums[j]),
            res >= 0,
    {
        
    }
}

}