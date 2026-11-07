impl Solution {
    pub fn predict_the_winner(nums: Vec<i32>) -> bool {
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
            dp[i] = nums[i] as i64;
            let mut j: usize = i + 1;
            while j < n {
                let prev_j = dp[j];
                let prev_jm1 = dp[j - 1];
                let left = nums[i] as i64 - prev_j;
                let right = nums[j] as i64 - prev_jm1;
                let val = Self::best_exec(left, right);
                dp[j] = val;
                j = j + 1;
            }
        }
        dp[n - 1] >= 0
    }

    fn best_exec(a: i64, b: i64) -> i64 {
        if a >= b { a } else { b }
    }
}
