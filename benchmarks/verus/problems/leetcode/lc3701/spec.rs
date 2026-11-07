use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alternating_prefix(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::alternating_prefix(s, end - 1)
                + if (end - 1) % 2 == 0 {
                    s[end - 1] as int
                } else {
                    -(s[end - 1] as int)
                }
        }
    }

    pub fn alternating_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::alternating_prefix(nums@, nums.len() as int),
    {
    }
}

}
