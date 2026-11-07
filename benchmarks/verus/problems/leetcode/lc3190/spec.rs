use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn minimum_operations(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 50,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            res == nums@.filter(|x: i32| x % 3 != 0).len(),
            0 <= res <= nums.len(),
    {
    }
}

}
