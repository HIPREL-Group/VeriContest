use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub open spec fn seq_min(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 1 {
            if end <= 0 { 0 } else { s[0] as int }
        } else {
            let prev = Self::seq_min(s, end - 1);
            let cur = s[end - 1] as int;
            if prev <= cur { prev } else { cur }
        }
    }

    pub open spec fn min_moves_spec(nums: Seq<i32>) -> int {
        let n = nums.len() as int;
        Self::seq_sum(nums, n) - n * Self::seq_min(nums, n)
    }

    pub fn min_moves(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==>
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            Self::min_moves_spec(nums@) >= -2_147_483_648,
            Self::min_moves_spec(nums@) <= 2_147_483_647,
        ensures
            result as int == Self::min_moves_spec(nums@),
    {
    }
}

}
