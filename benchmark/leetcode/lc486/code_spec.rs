use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn best(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn game_diff(nums: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i <= nums.len(),
            -1 <= j < nums.len(),
            i <= j + 1,
        decreases if i > j { 0int } else { j - i + 1 },
    {
        if i > j {
            0
        } else if i == j {
            nums[i] as int
        } else {
            Self::best(
                nums[i] as int - Self::game_diff(nums, i + 1, j),
                nums[j] as int - Self::game_diff(nums, i, j - 1),
            )
        }
    }

    pub fn predict_the_winner(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 20,
            forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 10_000_000,
        ensures
            result == (Self::game_diff(nums@, 0, nums.len() as int - 1) >= 0),
    {
        let n = nums.len();
        let mut dp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            dp.push(0);
            k = k + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            dp.set(i, nums[i] as i64);
            let mut j: usize = i + 1;
            while j < n {
                let prev_j = dp[j];
                let prev_jm1 = dp[j - 1];
                let left = nums[i] as i64 - prev_j;
                let right = nums[j] as i64 - prev_jm1;
                let val = Self::best_exec(left, right);
                dp.set(j, val);
                j = j + 1;
            }
        }
        dp[n - 1] >= 0
    }

    fn best_exec(a: i64, b: i64) -> (c: i64)
        ensures
            c as int == Self::best(a as int, b as int),
    {
        if a >= b { a } else { b }
    }
}

}
