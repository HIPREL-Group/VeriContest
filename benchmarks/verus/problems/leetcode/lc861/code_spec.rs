use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cols(grid: Seq<Vec<i32>>) -> int {
        if grid.len() > 0 { grid[0].len() as int } else { 0 }
    }

    pub open spec fn pow2(exp: int) -> int
        decreases exp,
    {
        if exp <= 0 { 1 } else { 2 * Self::pow2(exp - 1) }
    }

    pub open spec fn normalized_bit(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        recommends
            0 <= i < grid.len(),
            0 <= j < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
    {
        if grid[i][0] == 0 {
            1 - grid[i][j] as int
        } else {
            grid[i][j] as int
        }
    }

    pub open spec fn normalized_ones_prefix(grid: Seq<Vec<i32>>, j: int, rows_end: int) -> int
        recommends
            0 <= j < Self::cols(grid),
            0 <= rows_end <= grid.len(),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
        decreases rows_end,
    {
        if rows_end <= 0 {
            0
        } else {
            Self::normalized_ones_prefix(grid, j, rows_end - 1)
                + if Self::normalized_bit(grid, rows_end - 1, j) == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn best_ones_at(grid: Seq<Vec<i32>>, j: int) -> int
        recommends
            0 <= j < Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
    {
        let ones = Self::normalized_ones_prefix(grid, j, grid.len() as int);
        Self::max_int(ones, grid.len() - ones)
    }

    pub open spec fn score_rev_prefix(grid: Seq<Vec<i32>>, processed: int) -> int
        recommends
            0 <= processed <= Self::cols(grid),
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == Self::cols(grid),
        decreases processed,
    {
        if processed <= 0 {
            0
        } else {
            Self::score_rev_prefix(grid, processed - 1)
                + Self::best_ones_at(grid, Self::cols(grid) - processed) * Self::pow2(processed - 1)
        }
    }

    pub fn matrix_score(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 20,
            1 <= grid[0].len() <= 20,
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall|r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[0].len() ==> 0 <= #[trigger] grid[r][c] <= 1,
        ensures
            result as int == Self::score_rev_prefix(grid@, Self::cols(grid@)),
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut result: i32 = 0;
        let mut place: i32 = 1;
        let mut j: usize = cols;
        while j > 0 {
            let col = j - 1;
            let mut ones: i32 = 0;
            let mut i: usize = 0;
            while i < rows {
                let one = grid[i][col] == grid[i][0];
                if one {
                    ones = ones + 1;
                }
                i = i + 1;
            }
            let zeros = rows as i32 - ones;
            let best = if ones >= zeros { ones } else { zeros };
            result = result + best * place;
            place = place * 2;
            j = j - 1;
        }
        result
    }
}

}
