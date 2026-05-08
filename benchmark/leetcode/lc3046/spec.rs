use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_possible_to_split(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 100,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            res == (forall|i: int, j: int, k: int|
                0 <= i < j < k < nums.len() ==>
                !(nums[i] == nums[j] && nums[j] == nums[k])),
    {

    }
}

}
