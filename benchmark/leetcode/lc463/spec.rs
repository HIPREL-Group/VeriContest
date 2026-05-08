use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cell_contribution(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> int {
        if grid[r][c] == 1 {
            let top = if r > 0 && grid[r - 1][c] == 1 { 2int } else { 0int };
            let left = if c > 0 && grid[r][c - 1] == 1 { 2int } else { 0int };
            4 - top - left
        } else {
            0
        }
    }

    pub open spec fn row_perimeter(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c_end: int) -> int
        decreases c_end
    {
        if c_end <= 0 {
            0
        } else {
            Self::row_perimeter(grid, rows, cols, r, c_end - 1)
                + Self::cell_contribution(grid, rows, cols, r, c_end - 1)
        }
    }

    pub open spec fn island_perimeter_spec(grid: Seq<Vec<i32>>, rows: int, cols: int, r_end: int) -> int
        decreases r_end
    {
        if r_end <= 0 {
            0
        } else {
            Self::island_perimeter_spec(grid, rows, cols, r_end - 1)
                + Self::row_perimeter(grid, rows, cols, r_end - 1, cols)
        }
    }

    pub fn island_perimeter(grid: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= grid.len() <= 100,
            1 <= grid[0].len() <= 100,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len() ==> #[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1,
        ensures
            res as int == Self::island_perimeter_spec(grid@, grid.len() as int, grid[0].len() as int, grid.len() as int),
    {
    }
}

}
