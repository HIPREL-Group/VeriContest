impl Solution {
    pub fn change(amount: i32, coins: Vec<i32>) -> i32 {
        let amount_usize = amount as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= amount_usize {
            dp.push(0);
            k += 1;
        }
        dp[0] = 1;
        let mut i: usize = 0;
        while i < coins.len() {
            let coin = coins[i] as usize;
            let mut j: usize = coin;
            while j <= amount_usize {
                let old_dp_j = dp[j];
                let add = dp[j - coin];
                dp[j] = old_dp_j + add;
                j += 1;
            }
            i += 1;
        }
        dp[amount_usize]
    }
}
