use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_range(nums: &Vec<i32>, start: int, end: int) -> bool {
        forall|i: int, j: int| start <= i <= j < end ==> nums[i] <= nums[j]
    }

    pub open spec fn pivot_ok(nums: &Vec<i32>, p: int) -> bool {
        0 <= p < nums.len() && if p == 0 {
            Self::sorted_range(nums, 0, nums.len() as int)
        } else {
            nums[p - 1] > nums[p] && Self::sorted_range(nums, 0, p)
                && Self::sorted_range(nums, p, nums.len() as int)
                && forall|i: int, j: int|
                    p <= i < nums.len() && 0 <= j < p ==> nums[i] <= nums[j]
        }
    }

    pub open spec fn rotated_sorted(nums: &Vec<i32>) -> bool {
        exists|p: int| #[trigger] Self::pivot_ok(nums, p)
    }

    pub fn search(nums: Vec<i32>, target: i32) -> (result: bool)
        requires
            1 <= nums.len() <= 5_000,
            forall|i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            Self::rotated_sorted(&nums),
            -10_000 <= target <= 10_000,
        ensures
            result == (exists|i: int| 0 <= i < nums.len() && nums[i] == target),
    {
    }
}

}
