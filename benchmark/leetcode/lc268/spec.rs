use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains(nums: Seq<i32>, value: i32) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == value
    }

    pub fn missing_number(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= nums.len(),
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j], 
            exists |k: int| 0 <= k <= nums.len() && !(#[trigger] Self::contains(nums@, k as i32)),
        ensures 
            0 <= res <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> nums[i] != res, 
    {
        
    }
}

}