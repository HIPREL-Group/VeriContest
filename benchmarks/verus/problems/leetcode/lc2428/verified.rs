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
        proof {
            assert(0 < rows);
            assert(1 < rows);
            assert(2 < rows);
            assert(grid[0].len() == cols);
            assert(grid[1].len() == cols);
            assert(grid[2].len() == cols);
            assert(0 < cols);
            assert(1 < cols);
            assert(2 < cols);
        }
        let mut best = grid[0][0] + grid[0][1] + grid[0][2] + grid[1][1] + grid[2][0] + grid[2][1] + grid[2][2];

        proof {
            assert(best as int == hourglass_sum(grid@, 0, 0));
        }

        while i + 2 < rows
            invariant
                rows == grid.len(),
                cols == grid[0].len(),
                3 <= rows <= 150,
                3 <= cols <= 150,
                0 <= i <= rows,
                0 <= best_i && best_i + 2 < rows,
                0 <= best_j && best_j + 2 < cols,
                best as int == hourglass_sum(grid@, best_i as int, best_j as int),
                forall |r: int| 0 <= r < rows ==> 3 <= #[trigger] grid[r].len() <= 150,
                forall |r: int| 0 <= r < rows ==> #[trigger] grid[r].len() == cols,
                forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 0 <= #[trigger] grid[r][c] <= 1_000_000,
                forall |r: int, c: int| 0 <= r < i && 0 <= c && c + 2 < cols ==> #[trigger] hourglass_sum(grid@, r, c) <= best as int,
            decreases rows - i,
        {
            let mut j: usize = 0;
            while j + 2 < cols
                invariant
                    rows == grid.len(),
                    cols == grid[0].len(),
                    3 <= rows <= 150,
                    3 <= cols <= 150,
                    0 <= i && i + 2 < rows,
                    0 <= j <= cols,
                    0 <= best_i && best_i + 2 < rows,
                    0 <= best_j && best_j + 2 < cols,
                    best as int == hourglass_sum(grid@, best_i as int, best_j as int),
                    forall |r: int| 0 <= r < rows ==> 3 <= #[trigger] grid[r].len() <= 150,
                    forall |r: int| 0 <= r < rows ==> #[trigger] grid[r].len() == cols,
                    forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 0 <= #[trigger] grid[r][c] <= 1_000_000,
                    forall |r: int, c: int| 0 <= r < i && 0 <= c && c + 2 < cols ==> #[trigger] hourglass_sum(grid@, r, c) <= best as int,
                    forall |c: int| 0 <= c < j && c + 2 < cols ==> #[trigger] hourglass_sum(grid@, i as int, c) <= best as int,
                decreases cols - j,
            {
                proof {
                    assert(i + 2 < rows);
                    assert(j + 2 < cols);
                    assert(j < cols);
                    assert(j + 1 < cols);
                    assert(j + 2 < cols);
                    assert(i < rows);
                    assert(i + 1 < rows);
                    assert(i + 2 < rows);
                    assert(grid[i as int].len() == cols);
                    assert(grid[(i + 1) as int].len() == cols);
                    assert(grid[(i + 2) as int].len() == cols);
                    assert(j < grid[i as int].len());
                    assert(j + 1 < grid[i as int].len());
                    assert(j + 2 < grid[i as int].len());
                    assert(j + 1 < grid[(i + 1) as int].len());
                    assert(j < grid[(i + 2) as int].len());
                    assert(j + 1 < grid[(i + 2) as int].len());
                    assert(j + 2 < grid[(i + 2) as int].len());
                }
                let sum = grid[i][j]
                    + grid[i][j + 1]
                    + grid[i][j + 2]
                    + grid[i + 1][j + 1]
                    + grid[i + 2][j]
                    + grid[i + 2][j + 1]
                    + grid[i + 2][j + 2];
                proof {
                    assert(sum as int == hourglass_sum(grid@, i as int, j as int));
                }
                if sum > best {
                    let old_best = best;
                    best = sum;
                    best_i = i;
                    best_j = j;
                    proof {
                        assert((old_best as int) < (best as int));
                        assert(best as int == hourglass_sum(grid@, best_i as int, best_j as int));
                        assert forall |r: int, c: int| 0 <= r < i && 0 <= c && c + 2 < cols implies #[trigger] hourglass_sum(grid@, r, c) <= best as int by {
                            assert(hourglass_sum(grid@, r, c) <= old_best as int);
                        };
                        assert forall |c: int| 0 <= c < j && c + 2 < cols implies #[trigger] hourglass_sum(grid@, i as int, c) <= best as int by {
                            assert(hourglass_sum(grid@, i as int, c) <= old_best as int);
                        };
                    }
                } else {
                    proof {
                        assert(hourglass_sum(grid@, i as int, j as int) <= best as int);
                    }
                }
                j += 1;
            }
            proof {
                assert forall |r: int, c: int| 0 <= r < i + 1 && 0 <= c && c + 2 < cols implies #[trigger] hourglass_sum(grid@, r, c) <= best as int by {
                    if r < i {
                    } else {
                        assert(r == i);
                        assert(c + 2 < cols);
                        assert(!(j + 2 < cols));
                        assert(cols <= j + 2);
                        assert(c < j);
                    }
                };
            }
            i += 1;
        }

        proof {
            assert forall |r: int, c: int| 0 <= r && r + 2 < rows && 0 <= c && c + 2 < cols implies #[trigger] hourglass_sum(grid@, r, c) <= best as int by {
                assert(r + 2 < rows);
                assert(!(i + 2 < rows));
                assert(rows <= i + 2);
                assert(r < i);
            };
        }

        best
    }
}

}
