use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn satisfies_conditions(grid: Vec<Vec<i32>>) -> (result: bool)
        requires
            1 <= grid.len() <= 10,
            forall |i: int| 0 <= i < grid.len() ==> 1 <= #[trigger] grid[i].len() <= 10,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 9,
        ensures
            result == (
                (forall |i: int, j: int|
                    0 <= i && i + 1 < grid.len() && 0 <= j < grid[0].len() ==>
                    #[trigger] grid[i][j] == grid[i + 1][j])
                &&
                (forall |i: int, j: int|
                    0 <= i < grid.len() && 0 <= j && j + 1 < grid[0].len() ==>
                    #[trigger] grid[i][j] != grid[i][j + 1])
            ),
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut i: usize = 0;
        while i < rows
            invariant
                rows == grid.len(),
                cols == grid[0].len(),
                1 <= rows <= 10,
                1 <= cols <= 10,
                0 <= i <= rows,
                forall |r: int| 0 <= r < rows ==> 1 <= #[trigger] grid[r].len() <= 10,
                forall |r: int| 0 <= r < rows ==> #[trigger] grid[r].len() == cols,
                forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 0 <= #[trigger] grid[r][c] <= 9,
                forall |r: int, c: int|
                    0 <= r < i && 0 <= c < cols ==>
                    ((r + 1 < rows ==> #[trigger] grid[r][c] == grid[r + 1][c])
                    && (c + 1 < cols ==> #[trigger] grid[r][c] != grid[r][c + 1])),
            decreases rows - i,
        {
            let mut j: usize = 0;
            while j < cols
                invariant
                    rows == grid.len(),
                    cols == grid[0].len(),
                    1 <= rows <= 10,
                    1 <= cols <= 10,
                    0 <= i < rows,
                    0 <= j <= cols,
                    forall |r: int| 0 <= r < rows ==> 1 <= #[trigger] grid[r].len() <= 10,
                    forall |r: int| 0 <= r < rows ==> #[trigger] grid[r].len() == cols,
                    forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 0 <= #[trigger] grid[r][c] <= 9,
                    forall |r: int, c: int|
                        0 <= r < i && 0 <= c < cols ==>
                        ((r + 1 < rows ==> #[trigger] grid[r][c] == grid[r + 1][c])
                        && (c + 1 < cols ==> #[trigger] grid[r][c] != grid[r][c + 1])),
                    forall |c: int|
                        0 <= c < j ==>
                        ((i as int + 1 < rows ==> #[trigger] grid[i as int][c] == grid[i as int + 1][c])
                        && (c + 1 < cols ==> #[trigger] grid[i as int][c] != grid[i as int][c + 1])),
                decreases cols - j,
            {
                proof {
                    assert(i < rows);
                    assert(j < cols);
                    assert(grid[i as int].len() == cols);
                    if i + 1 < rows {
                        assert(grid[i as int + 1].len() == cols);
                    }
                }
                if i + 1 < rows && grid[i][j] != grid[i + 1][j] {
                    proof {
                        assert(!(forall |r: int, c: int|
                            0 <= r && r + 1 < grid.len() && 0 <= c < grid[0].len() ==> #[trigger] grid[r][c] == grid[r + 1][c])) by {
                            if forall |r: int, c: int|
                                0 <= r && r + 1 < grid.len() && 0 <= c < grid[0].len() ==> #[trigger] grid[r][c] == grid[r + 1][c]
                            {
                                assert(0 <= i as int);
                                assert((i as int) + 1 < grid.len());
                                assert(0 <= j as int);
                                assert((j as int) < grid[0].len());
                                assert(grid[i as int][j as int] == grid[i as int + 1][j as int]);
                                assert(false);
                            }
                        };
                    }
                    return false;
                }
                if j + 1 < cols && grid[i][j] == grid[i][j + 1] {
                    proof {
                        assert(!(forall |r: int, c: int|
                            0 <= r < grid.len() && 0 <= c && c + 1 < grid[0].len() ==> #[trigger] grid[r][c] != grid[r][c + 1])) by {
                            if forall |r: int, c: int|
                                0 <= r < grid.len() && 0 <= c && c + 1 < grid[0].len() ==> #[trigger] grid[r][c] != grid[r][c + 1]
                            {
                                assert(0 <= i as int);
                                assert((i as int) < grid.len());
                                assert(0 <= j as int);
                                assert((j as int) + 1 < grid[0].len());
                                assert(grid[i as int][j as int] != grid[i as int][j as int + 1]);
                                assert(false);
                            }
                        };
                    }
                    return false;
                }
                j = j + 1;
            }
            proof {
                assert(j == cols);
                assert forall |r: int, c: int|
                    0 <= r < i as int + 1 && 0 <= c < cols implies
                    ((r + 1 < rows ==> #[trigger] grid[r][c] == grid[r + 1][c])
                    && (c + 1 < cols ==> #[trigger] grid[r][c] != grid[r][c + 1])) by {
                    if r < i as int {
                    } else {
                        assert(r == i as int);
                    }
                };
            }
            i = i + 1;
        }
        proof {
            assert(i == rows);
            assert forall |r: int, c: int|
                0 <= r && r + 1 < grid.len() && 0 <= c < grid[0].len() implies #[trigger] grid[r][c] == grid[r + 1][c] by {
                assert(r < i as int);
            };
            assert forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c && c + 1 < grid[0].len() implies #[trigger] grid[r][c] != grid[r][c + 1] by {
                assert(r < i as int);
            };
        }
        true
    }
}

}
