impl Solution {
    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> i32
    {
        let t = target as usize;
        let mut dp: Vec<i64> = Vec::new();
        dp.push(1);
        let mut i: usize = 1;
        while i <= t {
            let mut total: i64 = 0;
            let mut j: usize = 0;
            while j < nums.len() {
                let num = nums[j] as usize;
                if num <= i {
                    total = total + dp[i - num];
                    if total > 2147483648 {
                        total = 2147483648;
                    }
                }
                j += 1;
            }
            dp.push(total);
            i += 1;
        }
        dp[t] as i32
    }
}
