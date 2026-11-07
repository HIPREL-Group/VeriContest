use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, end: nat) -> int
        decreases end,
    {
        if end == 0 {
            0
        } else {
            Self::prefix_sum(nums, (end - 1) as nat) + nums[(end - 1) as int] as int
        }
    }

    pub open spec fn seq_sum(nums: Seq<i32>) -> int {
        Self::prefix_sum(nums, nums.len() as nat)
    }

    pub open spec fn can_achieve(nums: Seq<i32>, end: nat, target: int) -> bool
        decreases end,
    {
        if target < 0 {
            false
        } else if end == 0 {
            target == 0
        } else {
            Self::can_achieve(nums, (end - 1) as nat, target)
            || Self::can_achieve(nums, (end - 1) as nat, target - nums[(end - 1) as int] as int)
        }
    }

    pub fn last_stone_weight_ii(stones: Vec<i32>) -> (result: i32)
        requires
            1 <= stones.len() <= 30,
            forall |i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 100,
        ensures
            0 <= result,
            result as int <= Self::seq_sum(stones@),
            (Self::seq_sum(stones@) - result as int) % 2 == 0,
            Self::can_achieve(stones@, stones.len() as nat, (Self::seq_sum(stones@) - result as int) / 2),
            forall |t: int| 0 <= t <= Self::seq_sum(stones@) / 2 && Self::can_achieve(stones@, stones.len() as nat, t)
                ==> Self::seq_sum(stones@) - 2 * t >= result as int,
    {
    }
}

}
