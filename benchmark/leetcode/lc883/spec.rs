use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_max_prefix(grid: Seq<Vec<i32>>, row: int, n: int) -> int
        recommends
            0 <= row < grid.len(),
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            let prev = Self::row_max_prefix(grid, row, n - 1);
            let cur = grid[row][n - 1] as int;
            if prev > cur { prev } else { cur }
        }
    }

    pub open spec fn col_max_prefix(grid: Seq<Vec<i32>>, col: int, n: int) -> int
        recommends
            0 <= col < grid.len(),
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            let prev = Self::col_max_prefix(grid, col, n - 1);
            let cur = grid[n - 1][col] as int;
            if prev > cur { prev } else { cur }
        }
    }

    pub open spec fn row_positive_prefix(grid: Seq<Vec<i32>>, row: int, n: int) -> int
        recommends
            0 <= row < grid.len(),
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::row_positive_prefix(grid, row, n - 1) + if grid[row][n - 1] > 0 { 1int } else { 0int }
        }
    }

    pub open spec fn row_max(grid: Seq<Vec<i32>>, row: int) -> int
        recommends
            0 <= row < grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        Self::row_max_prefix(grid, row, grid.len() as int)
    }

    pub open spec fn col_max(grid: Seq<Vec<i32>>, col: int) -> int
        recommends
            0 <= col < grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        Self::col_max_prefix(grid, col, grid.len() as int)
    }

    pub open spec fn row_positive_count(grid: Seq<Vec<i32>>, row: int) -> int
        recommends
            0 <= row < grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        Self::row_positive_prefix(grid, row, grid.len() as int)
    }

    pub open spec fn projection_area_spec(grid: Seq<Vec<i32>>, n: int) -> int
        recommends
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::projection_area_spec(grid, n - 1) + Self::row_max(grid, n - 1) + Self::col_max(grid, n - 1)
                + Self::row_positive_count(grid, n - 1)
        }
    }

    pub fn projection_area(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 50,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
        ensures
            result as int == Self::projection_area_spec(grid@, grid.len() as int),
    {
    }
}

}
