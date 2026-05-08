use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min_or_after_operations(nums: Seq<i32>, k: int) -> int {
        0
    }

    pub fn min_or_after_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            0 <= k < nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
        ensures
            result as int == Self::spec_min_or_after_operations(nums@, k as int),
    {
    }
}

}
