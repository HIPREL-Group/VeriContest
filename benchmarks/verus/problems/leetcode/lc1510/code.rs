impl Solution {
    pub fn winner_square_game(n: i32) -> bool {
        let n = n as usize;
        let mut dp: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i <= n {
            dp.push(false);
            i = i + 1;
        }
        i = 1;
        while i <= n {
            let mut k: usize = 1;
            let mut k_sq: usize = 1;
            let mut found: bool = false;
            while k_sq <= i && !found {
                if !dp[i - k_sq] {
                    found = true;
                }
                k = k + 1;
                k_sq = k_sq + 2 * k - 1;
            }
            if found {
                dp[i] = true;
            }
            i = i + 1;
        }
        dp[n]
    }
}
