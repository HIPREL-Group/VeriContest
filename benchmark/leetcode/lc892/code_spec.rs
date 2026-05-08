use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn cell_contrib(grid: Seq<Vec<i32>>, i: int, j: int, n: int) -> int
        recommends
            0 <= i < n,
            0 <= j < n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        let v = grid[i][j] as int;
        let base = if v > 0 { 4 * v + 2 } else { 0 };
        let up = if i > 0 { 2 * Self::spec_min(v, grid[i - 1][j] as int) } else { 0 };
        let left = if j > 0 { 2 * Self::spec_min(v, grid[i][j - 1] as int) } else { 0 };
        base - up - left
    }

    pub open spec fn row_sum(grid: Seq<Vec<i32>>, n: int, row: int, col_end: int) -> int
        recommends
            0 <= row < n,
            0 <= col_end <= n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases col_end,
    {
        if col_end <= 0 {
            0
        } else {
            Self::row_sum(grid, n, row, col_end - 1) + Self::cell_contrib(grid, row, col_end - 1, n)
        }
    }

    pub open spec fn surface_area_spec(grid: Seq<Vec<i32>>, n: int, row_end: int) -> int
        recommends
            0 <= row_end <= n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases row_end,
    {
        if row_end <= 0 {
            0
        } else {
            Self::surface_area_spec(grid, n, row_end - 1) + Self::row_sum(grid, n, row_end - 1, n)
        }
    }

    pub open spec fn surface_area_total(grid: Seq<Vec<i32>>, n: int) -> int
        recommends
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        Self::surface_area_spec(grid, n, n)
    }

    pub fn surface_area(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 50,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
        ensures
            result as int == Self::surface_area_total(grid@, grid.len() as int),
    {
        let n = grid.len();
        let mut res: i32 = 0;
        let mut i: usize = 0;

        while i < n
            decreases n - i,
        {
            let mut j: usize = 0;

            while j < n
                decreases n - j,
            {
                if grid[i][j] > 0 {
                    res = res + grid[i][j] * 4 + 2;
                }
                if i > 0 {
                    let a = grid[i][j];
                    let b = grid[i - 1][j];
                    let m = if a <= b { a } else { b };
                    res = res - m * 2;
                }
                if j > 0 {
                    let a = grid[i][j];
                    let b = grid[i][j - 1];
                    let m = if a <= b { a } else { b };
                    res = res - m * 2;
                }
                j += 1;
            }
            i += 1;
        }

        res
    }
}

}
