use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_removal(nums: Seq<i32>, r: int) -> bool {
        0 <= r < nums.len() &&
        (forall |j: int| 1 <= j < nums.len() && j != r && j - 1 != r ==>
            nums[j - 1] < #[trigger] nums[j]) &&
        (0 < r && r + 1 < nums.len() ==> nums[r - 1] < nums[r + 1])
    }

    pub fn can_be_increasing(nums: Vec<i32>) -> (result: bool)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result == (exists |r: int| Self::valid_removal(nums@, r)),
    {
    }
}

}
