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
        while i < m
            invariant
                1 <= m <= 100,
                m == grid.len(),
                n == grid[0].len(),
                forall |r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
                forall |r: int| 0 <= r < grid.len() ==> grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> -100 <= #[trigger] grid[r][c] <= 100,
                0 <= i <= m,
                0 <= count as int <= i as int * n as int,
                count as int == Self::count_neg_in_grid(grid@, i as int),
        {
            let mut j = 0;
            while j < n
                invariant
                    1 <= m <= 100,
                    m == grid.len(),
                    n == grid[0].len(),
                    forall |r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
                    forall |r: int| 0 <= r < grid.len() ==> grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> -100 <= #[trigger] grid[r][c] <= 100,
                    0 <= i < m,
                    0 <= j <= n,
                    0 <= count as int <= i as int * n as int + j as int,
                    count as int == Self::count_neg_in_grid(grid@, i as int) + Self::count_neg_in_row(grid[i as int]@, j as int),
                decreases n - j
            {
                proof {
                    assert(i < grid.len());
                    assert(grid[i as int].len() == n);
                    assert(j < grid[i as int].len());
                }
                if grid[i][j] < 0 {
                    assert((count as int) < 10000) by(nonlinear_arith)
                        requires
                            0 <= count as int,
                            count as int <= i as int * n as int + j as int,
                            j < n,
                            i < m,
                            m <= 100,
                            n <= 100,
                    {}
                    count += 1;
                }
                proof {
                    assert(Self::count_neg_in_row(grid[i as int]@, (j + 1) as int)
                        == Self::count_neg_in_row(grid[i as int]@, j as int)
                            + if grid[i as int][j as int] < 0 { 1int } else { 0int });
                }
                j += 1;
            }
            proof {
                assert(j == n);
                assert(0 <= count as int <= i as int * n as int + j as int);
                assert(0 <= count as int <= (i as int + 1) * n as int) by(nonlinear_arith)
                    requires
                        0 <= count as int,
                        count as int <= i as int * n as int + j as int,
                        j == n,
                        0 <= i as int,
                        0 <= n as int,
                {}
                assert((i + 1) as int > 0);
                assert(i < grid.len());
                assert(Self::count_neg_in_grid(grid@, (i + 1) as int)
                    == Self::count_neg_in_grid(grid@, i as int)
                        + Self::count_neg_in_row(grid[i as int]@, n as int));
            }
            i += 1;
        }
        count
    }
}
}
