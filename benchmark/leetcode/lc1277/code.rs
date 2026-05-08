impl Solution {
    fn set_dp(dp: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32) {
        let mut current_row = dp[row].clone();
        current_row[col] = value;
        dp[row] = current_row;
    }

    pub fn count_squares(matrix: Vec<Vec<i32>>) -> i32 {
        let m = matrix.len();
        let n = matrix[0].len();
        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                row.push(0);
                j = j + 1;
            }
            dp.push(row);
            i = i + 1;
        }
        let mut ans: i32 = 0;
        i = 0;
        while i < m {
            let mut j: usize = 0;
            while j < n {
                if matrix[i][j] == 1 {
                    if i == 0 || j == 0 {
                        Self::set_dp(&mut dp, i, j, 1);
                    } else {
                        let a = dp[i - 1][j];
                        let b = dp[i][j - 1];
                        let c = dp[i - 1][j - 1];
                        let min_val = if a <= b && a <= c { a } else if b <= c { b } else { c };
                        Self::set_dp(&mut dp, i, j, 1 + min_val);
                    }
                }
                ans = ans + dp[i][j];
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}
