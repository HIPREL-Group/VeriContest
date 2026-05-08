impl Solution {
    pub fn length_of_lis(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
        {
            dp.push(1i32);
            i += 1;
        }
        i = 1;
        while i < n
        {
            let mut j: usize = 0;
            while j < i
            {
                if nums[j] < nums[i] {
                    if dp[j] + 1 > dp[i] {
                        dp[i] = dp[j] + 1;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        let mut best = dp[0];
        let mut k: usize = 1;
        while k < n
        {
            if dp[k] > best {
                best = dp[k];
            }
            k += 1;
        }
        best
    }
}
