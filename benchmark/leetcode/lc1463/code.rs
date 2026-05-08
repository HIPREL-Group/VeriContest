impl Solution {
    fn max_i32(a: i32, b: i32) -> i32 {
        if a >= b { a } else { b }
    }

    pub fn cherry_pickup(grid: Vec<Vec<i32>>) -> i32 {
        let rows = grid.len();
        let cols = grid[0].len();
        let n = cols;
        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut c1: usize = 0;
        while c1 < n {
            let mut row_vec: Vec<i32> = Vec::new();
            let mut c2: usize = 0;
            while c2 < n {
                let val: i32 = if c1 == c2 {
                    grid[rows - 1][c1]
                } else {
                    grid[rows - 1][c1] + grid[rows - 1][c2]
                };
                row_vec.push(val);
                c2 += 1;
            }
            dp.push(row_vec);
            c1 += 1;
        }
        let mut ri: usize = 1;
        while ri < rows {
            let r = rows - 1 - ri;
            let mut new_dp: Vec<Vec<i32>> = Vec::new();
            let mut c1: usize = 0;
            while c1 < n {
                let mut row_vec: Vec<i32> = Vec::new();
                let mut c2: usize = 0;
                while c2 < n {
                    let cherries: i32 = if c1 == c2 { grid[r][c1] } else { grid[r][c1] + grid[r][c2] };
                    let v_1_1 = if c1 > 0 && c2 > 0 { dp[c1 - 1][c2 - 1] } else { 0 };
                    let v_10 = if c1 > 0 { dp[c1 - 1][c2] } else { 0 };
                    let v_11 = if c1 > 0 && c2 + 1 < n { dp[c1 - 1][c2 + 1] } else { 0 };
                    let v0_1 = if c2 > 0 { dp[c1][c2 - 1] } else { 0 };
                    let v00 = dp[c1][c2];
                    let v01 = if c2 + 1 < n { dp[c1][c2 + 1] } else { 0 };
                    let v1_1 = if c1 + 1 < n && c2 > 0 { dp[c1 + 1][c2 - 1] } else { 0 };
                    let v10 = if c1 + 1 < n { dp[c1 + 1][c2] } else { 0 };
                    let v11 = if c1 + 1 < n && c2 + 1 < n { dp[c1 + 1][c2 + 1] } else { 0 };
                    let best = Self::max_i32(
                        Self::max_i32(
                            Self::max_i32(v_1_1, v_10),
                            Self::max_i32(v_11, v0_1)
                        ),
                        Self::max_i32(
                            Self::max_i32(v00, v01),
                            Self::max_i32(v1_1, Self::max_i32(v10, v11))
                        )
                    );
                    row_vec.push(cherries + best);
                    c2 += 1;
                }
                new_dp.push(row_vec);
                c1 += 1;
            }
            dp = new_dp;
            ri += 1;
        }
        dp[0][n - 1]
    }
}
