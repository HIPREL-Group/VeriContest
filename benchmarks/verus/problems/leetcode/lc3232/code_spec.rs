use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_diff(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::digit_diff(s, end - 1) + if s[end - 1] < 10 { s[end - 1] as int } else { -(s[end - 1] as int) }
        }
    }

    pub fn can_alice_win(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 99,
        ensures
            res == (Self::digit_diff(nums@, nums.len() as int) != 0),
    {
        let mut diff: i32 = 0;
        for i in 0..nums.len()
        {
            if nums[i] < 10 {
                diff += nums[i];
            } else {
                diff -= nums[i];
            }
        }
        diff != 0
    }
}

}
