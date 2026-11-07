use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_value(nums: Seq<i32>, v: int) -> bool {
        exists|i: int| 0 <= i < nums.len() && nums[i] as int == v
    }

    pub fn first_missing_positive(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() >= 1,
            nums.len() <= 100_000,
        ensures
            result >= 1,
            !Self::contains_value(nums@, result as int),
            forall|v: int| 1 <= v < result as int ==> Self::contains_value(nums@, v),
    {
    }
}

} 
