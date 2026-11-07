use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;








pub open spec fn optimal_score(nums: Seq<i32>, mults: Seq<i32>, n: int, m: int, op: int, left: int) -> int
    decreases m - op
{
    if op >= m {
        0
    } else {
        let right_idx = n - 1 - (op - left);
        let take_left = mults[op] as int * nums[left] as int
            + optimal_score(nums, mults, n, m, op + 1, left + 1);
        let take_right = mults[op] as int * nums[right_idx] as int
            + optimal_score(nums, mults, n, m, op + 1, left);
        if take_left >= take_right { take_left } else { take_right }
    }
}

impl Solution {
    pub fn maximum_score(nums: Vec<i32>, multipliers: Vec<i32>) -> (result: i32)
        requires
            multipliers.len() >= 1,
            multipliers.len() <= 300,
            nums.len() >= multipliers.len(),
            nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
            forall|i: int| 0 <= i < multipliers.len() ==> -1000 <= #[trigger] multipliers[i] <= 1000,
        ensures
            result == optimal_score(nums@, multipliers@, nums@.len() as int, multipliers@.len() as int, 0, 0) as i32,
    {
        let n = nums.len();
        let m = multipliers.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= m {
            dp.push(0i32);
            k += 1;
        }
        let mut i: usize = m;
        while i > 0 {
            i -= 1;
            let mut j: usize = 0;
            while j <= i {
                let right_idx = n - 1 - (i - j);
                let left_choice = multipliers[i] * nums[j] + dp[j + 1];
                let right_choice = multipliers[i] * nums[right_idx] + dp[j];
                let val = if left_choice > right_choice { left_choice } else { right_choice };
                dp.set(j, val);
                j += 1;
            }
        }
        dp[0]
    }
}

}
