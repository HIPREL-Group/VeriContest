use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub open spec fn count_neg_in_row(row: Seq<i32>, j: int) -> int
        decreases j
    {
        if j <= 0 {
            0
        } else {
            Self::count_neg_in_row(row, j - 1) + if row[j - 1] < 0 { 1int } else { 0int }
        }
    }

    pub open spec fn count_neg_in_grid(grid: Seq<Vec<i32>>, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::count_neg_in_grid(grid, i - 1)
                + Self::count_neg_in_row(grid[i - 1]@, grid[i - 1].len() as int)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn count_negatives(grid: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= grid.len() <= 100,
            forall |r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> -100 <= #[trigger] grid[r][c] <= 100,
        ensures
            res as int == Self::count_neg_in_grid(grid@, grid.len() as int),
    {
        let m = grid.len();
        let n = grid[0].len();
        let mut count = 0;
        let mut i = 0;
        while i < m {
            let mut j = 0;
            while j < n {
                if grid[i][j] < 0 {
                    count += 1;
                }
                j += 1;
            }
            i += 1;
        }
        count
    }
}
}
