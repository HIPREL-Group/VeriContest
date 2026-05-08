use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn get_sum(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start, 
    {
        if start >= end {
            0
        } else {
            nums[start] + Self::get_sum(nums, start + 1, end)
        }
    }

    pub fn check_subarray_sum(nums: Vec<i32>, k: i32) -> (res: bool) 
        requires
            1 <= nums.len() <= 100_000, 
            forall |i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000, 
            forall |i: int, j: int| 0 <= i < j <= nums@.len() ==> 0 <= #[trigger] Self::get_sum(nums@, i, j) <= i32::MAX, 
            1 <= k <= i32::MAX, 
        ensures 
            res == (exists |i: int, j: int| 
                0 <= i < j <= nums@.len() && 
                j - i >= 2 &&
                Self::get_sum(nums@, i, j) % (k as int) == 0)
    {
        
    }
}

}