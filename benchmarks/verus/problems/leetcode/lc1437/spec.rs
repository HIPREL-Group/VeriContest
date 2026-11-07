use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn k_length_apart(nums: Vec<i32>, k: i32) -> (result: bool)
        requires
            1 <= nums.len() <= 100000,
            0 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1,
        ensures
            result == (forall |i: int, j: int| 0 <= i < j < nums.len() && #[trigger] nums[i] == 1 && #[trigger] nums[j] == 1 ==> j - i > k),
    {
    }
}

}
