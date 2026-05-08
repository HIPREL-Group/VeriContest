use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_max(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 1 {
            if end <= 0 { 0 } else { s[0] as int }
        } else {
            let prev = Self::seq_max(s, end - 1);
            let cur = s[end - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn seq_moves_to_target(s: Seq<i32>, target: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_moves_to_target(s, target, end - 1) + (target - s[end - 1] as int)
        }
    }

    pub open spec fn min_moves_spec(nums: Seq<i32>) -> int {
        let n = nums.len() as int;
        Self::seq_moves_to_target(nums, Self::seq_max(nums, n), n)
    }

    pub fn min_moves(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::min_moves_spec(nums@),
    {
    }
}

}
