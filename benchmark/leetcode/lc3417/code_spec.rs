use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn zigzag_col(grid: Seq<Vec<i32>>, row: int, step: int) -> int
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= row < grid.len(),
            0 <= step < grid[0].len(),
    {
        if row % 2 == 0 {
            step
        } else {
            grid[0].len() as int - 1 - step
        }
    }

    pub open spec fn zigzag_row_value(grid: Seq<Vec<i32>>, row: int, step: int) -> i32
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= row < grid.len(),
            0 <= step < grid[0].len(),
    {
        grid[row][Self::zigzag_col(grid, row, step)]
    }

    pub open spec fn take_after_steps(steps: int, take_start: bool) -> bool
        recommends
            0 <= steps,
        decreases steps,
    {
        if steps <= 0 {
            take_start
        } else {
            Self::take_after_steps(steps - 1, !take_start)
        }
    }

    pub open spec fn row_skip_prefix(grid: Seq<Vec<i32>>, row: int, upto: int, take_start: bool) -> Seq<i32>
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= row < grid.len(),
            0 <= upto <= grid[0].len(),
        decreases upto,
    {
        if upto <= 0 {
            seq![]
        } else {
            let prev = Self::row_skip_prefix(grid, row, upto - 1, take_start);
            let step = upto - 1;
            if Self::take_after_steps(step, take_start) {
                prev.push(Self::zigzag_row_value(grid, row, step))
            } else {
                prev
            }
        }
    }

    pub open spec fn rows_take_after(grid: Seq<Vec<i32>>, rows: int, take_start: bool) -> bool
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= rows <= grid.len(),
        decreases rows,
    {
        if rows <= 0 {
            take_start
        } else {
            let prev_take = Self::rows_take_after(grid, rows - 1, take_start);
            Self::take_after_steps(grid[0].len() as int, prev_take)
        }
    }

    pub open spec fn zigzag_skip_rows_prefix(grid: Seq<Vec<i32>>, rows: int, take_start: bool) -> Seq<i32>
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            0 <= rows <= grid.len(),
        decreases rows,
    {
        if rows <= 0 {
            seq![]
        } else {
            let prev = Self::zigzag_skip_rows_prefix(grid, rows - 1, take_start);
            let row_take_start = Self::rows_take_after(grid, rows - 1, take_start);
            prev + Self::row_skip_prefix(grid, rows - 1, grid[0].len() as int, row_take_start)
        }
    }

    pub open spec fn zigzag_skip_result(grid: Seq<Vec<i32>>) -> Seq<i32>
        recommends
            1 <= grid.len(),
            1 <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        Self::zigzag_skip_rows_prefix(grid, grid.len() as int, true)
    }

    pub fn zigzag_traversal(grid: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            2 <= grid.len() <= 50,
            2 <= grid[0].len() <= 50,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 2500,
        ensures
            result@ == Self::zigzag_skip_result(grid@),
    {
        let m = grid.len();
        let n = grid[0].len();
        let mut result: Vec<i32> = Vec::new();
        let mut take = true;
        let mut i: usize = 0;
        while i < m {
            let mut s: usize = 0;
            while s < n {
                let col = if i % 2 == 0 { s } else { n - 1 - s };
                let v = grid[i][col];
                if take {
                    result.push(v);
                }
                take = !take;
                s += 1;
            }
            i += 1;
        }
        result
    }
}

}
