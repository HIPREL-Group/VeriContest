impl Solution {
    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> i32 {
        let target_usize = target as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= target_usize {
            dp.push(0);
            k += 1;
        }
        dp[0] = 1;
        let mut i: usize = 1;
        while i <= target_usize {
            let mut total: i32 = 0;
            let mut j: usize = 0;
            while j < nums.len() {
                let num = nums[j];
                if num <= i as i32 {
                    total = total + dp[i - num as usize];
                }
                j += 1;
            }
            dp[i] = total;
            i += 1;
        }
        dp[target_usize]
    }
}
