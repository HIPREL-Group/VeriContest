impl Solution {
    fn min_i32(a: i32, b: i32) -> i32 {
        if a <= b { a } else { b }
    }

    pub fn minimum_total(triangle: Vec<Vec<i32>>) -> i32 {
        let rows = triangle.len();
        let mut dp = triangle[rows - 1].clone();
        let mut row = rows - 1;
        while row > 0 {
            row = row - 1;
            let mut col = 0usize;
            while col <= row {
                let best_child = Self::min_i32(dp[col], dp[col + 1]);
                let value = triangle[row][col] + best_child;
                dp[col] = value;
                col = col + 1;
            }
        }
        dp[0]
    }
}
