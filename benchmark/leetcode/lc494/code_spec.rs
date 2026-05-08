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
        let n = nums.len();
        let mut total = 0i32;
        let mut i = 0usize;
        while i < n
        {
            total = total + nums[i];
            i += 1;
        }
        let transformed = total + target;
        if transformed < 0 {
            return 0;
        }
        if transformed % 2 != 0 {
            return 0;
        }
        let goal_i = transformed / 2;
        let goal = goal_i as usize;
        if goal_i > total {
            return 0;
        }
        let goal_len = goal + 1;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < goal_len
        {
            dp.push(0);
            k += 1;
        }
        dp[0] = 1;
        let mut idx: usize = 0;
        while idx < n
        {
            let num = nums[idx] as usize;
            let mut s = goal_len;
            while s > 0
            {
                let cur = s - 1;
                if num <= cur {
                    let old_value = dp[cur];
                    let add_value = dp[cur - num];
                    dp[cur] = old_value + add_value;
                }
                s = cur;
            }
            idx += 1;
        }
        dp[goal]
    }
}

}
