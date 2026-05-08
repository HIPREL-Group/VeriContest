impl Solution {
    pub fn stone_game_vii(stones: Vec<i32>) -> i32
    {
        let n = stones.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            dp.push(0i32);
            k = k + 1;
        }
        let mut i: i32 = n as i32 - 2;
        while i >= 0 {
            let mut total: i32 = stones[i as usize];
            let mut j: usize = (i + 1) as usize;
            while j < n {
                total = total + stones[j];
                let left = total - stones[i as usize] - dp[j];
                let right = total - stones[j] - dp[j - 1];
                if left >= right {
                    dp[j] = left;
                } else {
                    dp[j] = right;
                }
                j = j + 1;
            }
            i = i - 1;
        }
        dp[n - 1]
    }
}
