impl Solution {
    pub fn min_falling_path_sum(grid: Vec<Vec<i32>>) -> i32 {
        let n = grid.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k = 0usize;
        while k < n {
            dp.push(grid[n - 1][k]);
            k = k + 1;
        }
        let mut row = n - 1;
        while row > 0 {
            row = row - 1;
            let mut min1 = dp[0];
            let mut min1_idx: usize = 0;
            let mut min2 = i32::MAX;
            let mut k = 1usize;
            while k < n {
                if dp[k] < min1 {
                    min2 = min1;
                    min1 = dp[k];
                    min1_idx = k;
                } else if dp[k] < min2 {
                    min2 = dp[k];
                }
                k = k + 1;
            }
            let mut j = 0usize;
            while j < n {
                if j == min1_idx {
                    dp[j] = grid[row][j] + min2;
                } else {
                    dp[j] = grid[row][j] + min1;
                }
                j = j + 1;
            }
        }
        let mut result = dp[0];
        let mut k = 1usize;
        while k < n {
            if dp[k] < result {
                result = dp[k];
            }
            k = k + 1;
        }
        result
    }
}
