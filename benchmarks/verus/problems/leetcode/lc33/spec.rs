use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ord_tuple(small: &(bool, i32), big: &(bool, i32)) -> bool {
        if small.0 != big.0 {
            !small.0 && big.0
        } else {
            small.1 < big.1
        }
    }

    pub open spec fn rot_tuple(nums: &Vec<i32>, i: int) -> (bool, i32) {
        if 0 <= i < nums.len() {
            (nums[i] < nums[0], nums[i])
        } else {
            (false, 0)
        }
    }

    pub fn search(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 5_000,
            forall|i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            forall|i: int, j: int|
                0 <= i < j < nums.len() ==> #[trigger] Self::ord_tuple(
                    &Self::rot_tuple(&nums, i),
                    &Self::rot_tuple(&nums, j),
                ),
            -10_000 <= target <= 10_000,
        ensures
            res == -1 || 0 <= res < nums.len(),
            0 <= res < nums.len() ==> target == nums[res as int],
            res == -1 ==> forall|i: int| 0 <= i < nums.len() ==> nums[i] != target,
    {
    }
}

} 
