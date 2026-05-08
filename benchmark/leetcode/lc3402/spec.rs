use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adjusted_col_val(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        decreases row,
    {
        if row <= 0 {
            grid[0][col] as int
        } else {
            let prev = Self::adjusted_col_val(grid, row - 1, col);
            if (grid[row][col] as int) <= prev {
                prev + 1
            } else {
                grid[row][col] as int
            }
        }
    }

    pub open spec fn col_ops_prefix(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        decreases row,
    {
        if row <= 0 {
            0int
        } else {
            Self::col_ops_prefix(grid, row - 1, col)
                + (Self::adjusted_col_val(grid, row, col) - grid[row][col] as int)
        }
    }

    pub open spec fn total_ops_cols(grid: Seq<Vec<i32>>, cols: int) -> int
        decreases cols,
    {
        if cols <= 0 {
            0int
        } else {
            Self::total_ops_cols(grid, cols - 1)
                + Self::col_ops_prefix(grid, grid.len() as int - 1, cols - 1)
        }
    }

    pub fn minimum_operations(grid: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= grid.len() <= 50,
            1 <= grid[0].len() <= 50,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
        ensures
            res as int == Self::total_ops_cols(grid@, grid[0].len() as int),
    {
    }
}

} 
