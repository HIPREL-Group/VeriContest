use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::spec_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub fn running_sum(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() as int ==> result[i] == Self::spec_sum(nums@, i + 1),
    {
        
    }
}

}
