use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(nums: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        spec_sum(nums, lo, hi - 1) + nums[hi - 1] as int
    }
}

pub open spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

impl Solution {
    pub fn left_right_difference(nums: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            answer.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==>
                #[trigger] answer[i] == spec_abs(
                    spec_sum(nums@, 0, i) - spec_sum(nums@, i + 1, nums.len() as int)
                ),
    {
    }
}

} 
