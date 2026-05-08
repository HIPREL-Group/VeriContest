use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    
    
    pub open spec fn cherry_value(grid: Seq<Vec<i32>>, row: int, c1: int, c2: int) -> int {
        if c1 == c2 {
            grid[row][c1] as int
        } else {
            grid[row][c1] as int + grid[row][c2] as int
        }
    }

    
    
    
    
    
    
    
    pub open spec fn dp_val(grid: Seq<Vec<i32>>, row: int, c1: int, c2: int) -> int
        decreases grid.len() - row
    {
        let n = grid[0].len() as int;
        if row < 0 || row >= grid.len() || c1 < 0 || c1 >= n || c2 < 0 || c2 >= n {
            0
        } else if row >= grid.len() - 1 {
            Self::cherry_value(grid, row, c1, c2)
        } else {
            Self::cherry_value(grid, row, c1, c2) + Self::max2(
                Self::max2(
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 - 1, c2 - 1),
                        Self::dp_val(grid, row + 1, c1 - 1, c2)
                    ),
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 - 1, c2 + 1),
                        Self::dp_val(grid, row + 1, c1, c2 - 1)
                    )
                ),
                Self::max2(
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1, c2),
                        Self::dp_val(grid, row + 1, c1, c2 + 1)
                    ),
                    Self::max2(
                        Self::dp_val(grid, row + 1, c1 + 1, c2 - 1),
                        Self::max2(
                            Self::dp_val(grid, row + 1, c1 + 1, c2),
                            Self::dp_val(grid, row + 1, c1 + 1, c2 + 1)
                        )
                    )
                )
            )
        }
    }

    fn max_i32(a: i32, b: i32) -> (res: i32)
        ensures
            res as int == Self::max2(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    pub fn cherry_pickup(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= grid.len() <= 70,
            2 <= grid[0].len() <= 70,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 100,
        ensures
            result as int == Self::dp_val(grid@, 0, 0, grid[0].len() as int - 1),
    {
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

}
