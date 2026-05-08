use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn increasing_triplet(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 500_000,
        ensures
            res == (exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() && nums[a] < nums[b] && nums[b] < nums[c]),
    {
        
    }
}

}
