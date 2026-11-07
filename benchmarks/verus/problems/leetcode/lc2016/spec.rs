use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn maximum_difference(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            res == -1 || res >= 1,
            res == -1 ==>
                forall |a: int, b: int| 0 <= a < b < nums.len() as int
                    ==> nums[a] >= nums[b],
            res >= 1 ==>
                exists |a: int, b: int| 0 <= a < b < nums.len() as int
                    && nums[a] < nums[b]
                    && res == nums[b] - nums[a],
            res >= 1 ==>
                forall |a: int, b: int| 0 <= a < b < nums.len() as int
                    && nums[a] < nums[b]
                    ==> nums[b] - nums[a] <= res,
    {
    }
}

} 
