impl Solution {
    pub fn maximum_score(nums: Vec<i32>, multipliers: Vec<i32>) -> i32 {
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
                dp[j] = val;
                j += 1;
            }
        }
        dp[0]
    }
}
