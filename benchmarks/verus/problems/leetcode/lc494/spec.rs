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

    pub open spec fn target_sum_count_prefix(nums: Seq<i32>, end: nat, target: int) -> int
        decreases end,
    {
        if end == 0 {
            if target == 0 { 1 } else { 0 }
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            Self::target_sum_count_prefix(nums, (end - 1) as nat, target - x)
                + Self::target_sum_count_prefix(nums, (end - 1) as nat, target + x)
        }
    }

    pub open spec fn target_sum_count(nums: Seq<i32>, target: int) -> int {
        Self::target_sum_count_prefix(nums, nums.len() as nat, target)
    }

    pub fn find_target_sum_ways(nums: Vec<i32>, target: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 20,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            Self::seq_sum(nums@) <= 1000,
            -1000 <= target <= 1000,
        ensures
            result as int == Self::target_sum_count(nums@, target as int),
    {
    }
}

}
