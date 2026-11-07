use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_prefix(nums: Seq<i32>, len: int) -> bool
        decreases len,
    {
        if len <= 0 {
            true
        } else if len == 1 {
            false
        } else {
            let two_equal = nums[len - 2] == nums[len - 1] && Self::valid_prefix(nums, len - 2);
            let three_equal = len >= 3
                && nums[len - 3] == nums[len - 2]
                && nums[len - 2] == nums[len - 1]
                && Self::valid_prefix(nums, len - 3);
            let three_inc = len >= 3
                && nums[len - 3] + 1 == nums[len - 2]
                && nums[len - 2] + 1 == nums[len - 1]
                && Self::valid_prefix(nums, len - 3);
            two_equal || three_equal || three_inc
        }
    }

    pub fn valid_partition(nums: Vec<i32>) -> (ans: bool)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
        ensures
            ans == Self::valid_prefix(nums@, nums.len() as int),
    {
    }
}

}
