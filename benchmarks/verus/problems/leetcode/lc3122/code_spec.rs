use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn big_cost() -> int {
        1_000_000_000int
    }

    pub open spec fn col_count_prefix(grid: Seq<Vec<i32>>, col: int, val: int, rows: int) -> int
        recommends
            grid.len() > 0,
            0 <= rows <= grid.len(),
            0 <= col < grid[0].len(),
            0 <= val < 10,
        decreases rows,
    {
        if rows <= 0 {
            0
        } else {
            Self::col_count_prefix(grid, col, val, rows - 1)
                + if grid[rows - 1][col] == val as i32 { 1int } else { 0int }
        }
    }

    pub open spec fn col_cost(grid: Seq<Vec<i32>>, col: int, val: int) -> int
        recommends
            grid.len() > 0,
            0 <= col < grid[0].len(),
            0 <= val < 10,
    {
        grid.len() as int - Self::col_count_prefix(grid, col, val, grid.len() as int)
    }

    pub open spec fn min_cost_prefix_last(grid: Seq<Vec<i32>>, cols: int, last: int) -> int
        recommends
            grid.len() > 0,
            1 <= cols <= grid[0].len(),
            0 <= last < 10,
        decreases cols, 0int,
    {
        if cols <= 1 {
            Self::col_cost(grid, 0, last)
        } else {
            Self::col_cost(grid, cols - 1, last)
                + Self::min_prev_prefix(grid, cols - 1, last, 10)
        }
    }

    pub open spec fn min_prev_prefix(grid: Seq<Vec<i32>>, cols: int, last: int, upto: int) -> int
        recommends
            grid.len() > 0,
            1 <= cols <= grid[0].len(),
            0 <= last < 10,
            0 <= upto <= 10,
        decreases cols, 1int, upto,
    {
        if upto <= 0 {
            Self::big_cost()
        } else {
            let rest = Self::min_prev_prefix(grid, cols, last, upto - 1);
            let cand = upto - 1;
            if cand == last {
                rest
            } else {
                let cur = Self::min_cost_prefix_last(grid, cols, cand);
                if cur <= rest { cur } else { rest }
            }
        }
    }

    pub open spec fn min_total_prefix(grid: Seq<Vec<i32>>, cols: int, upto: int) -> int
        recommends
            grid.len() > 0,
            1 <= cols <= grid[0].len(),
            0 <= upto <= 10,
        decreases upto,
    {
        if upto <= 0 {
            Self::big_cost()
        } else {
            let rest = Self::min_total_prefix(grid, cols, upto - 1);
            let cand = upto - 1;
            let cur = Self::min_cost_prefix_last(grid, cols, cand);
            if cur <= rest { cur } else { rest }
        }
    }

    pub open spec fn min_operations_spec(grid: Seq<Vec<i32>>) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
    {
        Self::min_total_prefix(grid, grid[0].len() as int, 10)
    }

    pub fn minimum_operations(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 1000,
            1 <= grid[0].len() <= 1000,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
        ensures
            result as int == Self::min_operations_spec(grid@),
    {
        let m = grid.len();
        let n = grid[0].len();
        let m_i64 = m as i64;

        let mut dp_prev: Vec<i64> = Vec::new();
        let mut v: usize = 0;
        while v < 10 {
            let mut matches: i64 = 0;
            let mut i: usize = 0;
            while i < m {
                if grid[i][0] == v as i32 {
                    matches = matches + 1;
                }
                i = i + 1;
            }
            let cost = m_i64 - matches;
            dp_prev.push(cost);
            v = v + 1;
        }

        let mut col: usize = 1;
        while col < n {
            let mut dp_cur: Vec<i64> = Vec::new();
            v = 0;
            while v < 10 {
                let mut matches: i64 = 0;
                let mut i: usize = 0;
                while i < m {
                    if grid[i][col] == v as i32 {
                        matches = matches + 1;
                    }
                    i = i + 1;
                }
                let cost = m_i64 - matches;

                let mut best: i64 = 1_000_000_000;
                let mut u: usize = 0;
                while u < 10 {
                    if u != v && dp_prev[u] < best {
                        best = dp_prev[u];
                    }
                    u = u + 1;
                }

                let value = cost + best;
                dp_cur.push(value);
                v = v + 1;
            }
            dp_prev = dp_cur;
            col = col + 1;
        }

        let mut answer: i64 = 1_000_000_000;
        v = 0;
        while v < 10 {
            if dp_prev[v] < answer {
                answer = dp_prev[v];
            }
            v = v + 1;
        }

        answer as i32
    }
}

}
