use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn dp_end(nums: Seq<i32>, k: int) -> int
        decreases if k <= 0 { 0int } else { k }
    {
        if k <= 0 {
            -1
        } else {
            let prev = Self::dp_end(nums, k - 1);
            if k >= 2 && prev > 0 && nums[k] == nums[k - 2] {
                prev + 1
            } else if nums[k] == nums[k - 1] + 1 {
                2
            } else {
                -1
            }
        }
    }

    pub open spec fn best_upto(nums: Seq<i32>, k: int) -> int
        decreases if k <= 0 { 0int } else { k }
    {
        if k <= 0 {
            -1
        } else {
            let prev = Self::best_upto(nums, k - 1);
            let cur = Self::dp_end(nums, k);
            if prev >= cur { prev } else { cur }
        }
    }

    pub fn alternating_subarray(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            result as int == Self::best_upto(nums@, nums.len() as int - 1),
    {
    }
}

}
