use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_peak_element(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] != nums[i + 1],
        ensures
            0 <= result < nums.len(),
            (result == 0 || nums[result as int] > nums[result as int - 1]),
            (result == nums.len() - 1 || nums[result as int] > nums[result as int + 1]),
    {
    }
}

}
