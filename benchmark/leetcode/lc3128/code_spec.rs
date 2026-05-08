use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_ones_prefix(grid: Seq<Vec<i32>>, row: int, upto: int) -> int
        recommends
            grid.len() > 0,
            0 <= row < grid.len(),
            0 <= upto <= grid[row].len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::row_ones_prefix(grid, row, upto - 1)
                + if grid[row][upto - 1] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn row_ones(grid: Seq<Vec<i32>>, row: int) -> int
        recommends
            grid.len() > 0,
            0 <= row < grid.len(),
    {
        Self::row_ones_prefix(grid, row, grid[row].len() as int)
    }

    pub open spec fn col_ones_prefix(grid: Seq<Vec<i32>>, col: int, upto: int) -> int
        recommends
            grid.len() > 0,
            0 <= col < grid[0].len(),
            0 <= upto <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::col_ones_prefix(grid, col, upto - 1)
                + if grid[upto - 1][col] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn col_ones(grid: Seq<Vec<i32>>, col: int) -> int
        recommends
            grid.len() > 0,
            0 <= col < grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        Self::col_ones_prefix(grid, col, grid.len() as int)
    }

    pub open spec fn triangle_at(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            0 <= row < grid.len(),
            0 <= col < grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        if grid[row][col] == 1 {
            (Self::row_ones(grid, row) - 1) * (Self::col_ones(grid, col) - 1)
        } else {
            0
        }
    }

    pub open spec fn row_triangle_sum_prefix(grid: Seq<Vec<i32>>, row: int, upto: int) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            0 <= row < grid.len(),
            0 <= upto <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::row_triangle_sum_prefix(grid, row, upto - 1)
                + Self::triangle_at(grid, row, upto - 1)
        }
    }

    pub open spec fn total_triangle_sum_prefix(grid: Seq<Vec<i32>>, upto_rows: int) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            0 <= upto_rows <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        decreases upto_rows,
    {
        if upto_rows <= 0 {
            0
        } else {
            Self::total_triangle_sum_prefix(grid, upto_rows - 1)
                + Self::row_triangle_sum_prefix(grid, upto_rows - 1, grid[0].len() as int)
        }
    }

    pub open spec fn right_triangles_spec(grid: Seq<Vec<i32>>) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        Self::total_triangle_sum_prefix(grid, grid.len() as int)
    }

    pub fn number_of_right_triangles(grid: Vec<Vec<i32>>) -> (result: i64)
        requires
            1 <= grid.len() <= 1000,
            1 <= grid[0].len() <= 1000,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> {
                let v = #[trigger] grid[r][c];
                v == 0 || v == 1
            },
        ensures
            result as int == Self::right_triangles_spec(grid@),
    {
        let m = grid.len();
        let n = grid[0].len();

        let mut row_counts: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row_sum: i64 = 0;
            let mut j: usize = 0;
            while j < n {
                if grid[i][j] == 1 {
                    row_sum = row_sum + 1;
                }
                j = j + 1;
            }
            row_counts.push(row_sum);
            i = i + 1;
        }

        let mut col_counts: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut col_sum: i64 = 0;
            i = 0;
            while i < m {
                if grid[i][j] == 1 {
                    col_sum = col_sum + 1;
                }
                i = i + 1;
            }
            col_counts.push(col_sum);
            j = j + 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < m {
            j = 0;
            while j < n {
                if grid[i][j] == 1 {
                    let add = (row_counts[i] - 1) * (col_counts[j] - 1);
                    ans = ans + add;
                }
                j = j + 1;
            }
            i = i + 1;
        }

        ans
    }
}

}
