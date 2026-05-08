use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn col_sum(grid: Seq<Vec<i32>>, rows: int, c: int) -> int
        decreases rows,
    {
        if rows <= 0 {
            0
        } else {
            Self::col_sum(grid, rows - 1, c) + grid[rows - 1][c] as int
        }
    }

    pub open spec fn rect_sum(grid: Seq<Vec<i32>>, rows: int, cols: int) -> int
        decreases cols,
    {
        if rows <= 0 || cols <= 0 {
            0
        } else {
            Self::rect_sum(grid, rows, cols - 1) + Self::col_sum(grid, rows, cols - 1)
        }
    }

    pub open spec fn row_count(grid: Seq<Vec<i32>>, k: int, r: int, cols: int) -> int
        decreases cols,
    {
        if cols <= 0 {
            0
        } else {
            Self::row_count(grid, k, r, cols - 1)
                + if Self::rect_sum(grid, r + 1, cols) <= k { 1int } else { 0int }
        }
    }

    pub open spec fn total_count(grid: Seq<Vec<i32>>, k: int, rows: int) -> int
        decreases rows,
    {
        if rows <= 0 {
            0
        } else {
            Self::total_count(grid, k, rows - 1)
                + Self::row_count(grid, k, rows - 1, grid[0].len() as int)
        }
    }

    pub open spec fn count_submatrices_spec(grid: Seq<Vec<i32>>, k: int) -> int {
        Self::total_count(grid, k, grid.len() as int)
    }

    pub fn count_submatrices(grid: Vec<Vec<i32>>, k: i32) -> (result: i32)
        requires
            1 <= grid.len() <= 1000,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            1 <= grid[0].len() <= 1000,
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 1000,
            1 <= k <= 1_000_000_000,
        ensures
            result as int == Self::count_submatrices_spec(grid@, k as int),
    {
    }
}

}
