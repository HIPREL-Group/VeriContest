use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_subarrays(nums: Vec<i32>) -> (result: bool)
        requires
            2 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result == (exists|i: int, j: int|
                0 <= i < j && j + 1 < nums.len() as int
                && (#[trigger] nums[i]) as int + nums[i + 1] as int == (#[trigger] nums[j]) as int + nums[j + 1] as int),
    {
    }
}

}
