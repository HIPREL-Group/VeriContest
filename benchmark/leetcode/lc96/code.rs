impl Solution {
    pub fn num_trees(n: i32) -> i32 {
        let mut dp: Vec<i32> = Vec::new();
        dp.push(1i32);
        dp.push(1i32);
        let mut i: usize = 2;
        while i <= n as usize {
            let mut sum: i32 = 0;
            let mut j: usize = 0;
            while j < i {
                let dj = dp[j];
                let dimj = dp[i - 1 - j];
                sum = sum + dj * dimj;
                j = j + 1;
            }
            dp.push(sum);
            i = i + 1;
        }
        dp[n as usize]
    }
}
