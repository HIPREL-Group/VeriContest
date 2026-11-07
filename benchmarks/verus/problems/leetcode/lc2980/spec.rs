use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn has_trailing_zeros(nums: Vec<i32>) -> (result: bool)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] % 2 == 0 && nums[j] % 2 == 0),
    {
    }
}

}
