use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn hourglass_sum(grid: Seq<Vec<i32>>, i: int, j: int) -> int
    recommends
        0 <= i,
        0 <= j,
        i + 2 < grid.len(),
        grid.len() > 0,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        j + 2 < grid[0].len(),
{
    grid[i][j] as int + grid[i][j + 1] as int + grid[i][j + 2] as int + grid[i + 1][j + 1] as int
        + grid[i + 2][j] as int + grid[i + 2][j + 1] as int + grid[i + 2][j + 2] as int
}

impl Solution {
    pub fn max_sum(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            3 <= grid.len() <= 150,
            forall |i: int| 0 <= i < grid.len() ==> 3 <= #[trigger] grid[i].len() <= 150,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 1_000_000,
        ensures
            exists |i: int, j: int|
                0 <= i && i + 2 < grid.len() && 0 <= j && j + 2 < grid[0].len() && result as int == hourglass_sum(grid@, i, j),
            forall |i: int, j: int|
                0 <= i && i + 2 < grid.len() && 0 <= j && j + 2 < grid[0].len() ==> hourglass_sum(grid@, i, j) <= result as int,
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut i: usize = 0;
        let mut best_i: usize = 0;
        let mut best_j: usize = 0;
        let mut best = grid[0][0] + grid[0][1] + grid[0][2] + grid[1][1] + grid[2][0] + grid[2][1] + grid[2][2];

        while i + 2 < rows {
            let mut j: usize = 0;
            while j + 2 < cols {
                let sum = grid[i][j]
                    + grid[i][j + 1]
                    + grid[i][j + 2]
                    + grid[i + 1][j + 1]
                    + grid[i + 2][j]
                    + grid[i + 2][j + 1]
                    + grid[i + 2][j + 2];
                if sum > best {
                    let old_best = best;
                    best = sum;
                    best_i = i;
                    best_j = j;
                }
                j += 1;
            }
            i += 1;
        }

        best
    }
}

}
