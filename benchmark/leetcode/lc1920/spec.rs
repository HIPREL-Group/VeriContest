use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn build_array(nums: Vec<i32>) -> (ans: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
        ensures
            ans.len() == nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] ans[i] == nums[nums[i] as int],
    {
    }
}

}
