use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adjusted_col_val(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        decreases row,
    {
        if row <= 0 {
            grid[0][col] as int
        } else {
            let prev = Self::adjusted_col_val(grid, row - 1, col);
            if (grid[row][col] as int) <= prev {
                prev + 1
            } else {
                grid[row][col] as int
            }
        }
    }

    pub open spec fn col_ops_prefix(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        decreases row,
    {
        if row <= 0 {
            0int
        } else {
            Self::col_ops_prefix(grid, row - 1, col)
                + (Self::adjusted_col_val(grid, row, col) - grid[row][col] as int)
        }
    }

    pub open spec fn total_ops_cols(grid: Seq<Vec<i32>>, cols: int) -> int
        decreases cols,
    {
        if cols <= 0 {
            0int
        } else {
            Self::total_ops_cols(grid, cols - 1)
                + Self::col_ops_prefix(grid, grid.len() as int - 1, cols - 1)
        }
    }

    pub fn minimum_operations(grid: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= grid.len() <= 50,
            1 <= grid[0].len() <= 50,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
        ensures
            res as int == Self::total_ops_cols(grid@, grid[0].len() as int),
    {
        let m = grid.len();
        let n = grid[0].len();
        let mut ops: i64 = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                m == grid.len(),
                n == grid[0].len(),
                1 <= m <= 50,
                1 <= n <= 50,
                forall |r: int| 0 <= r < m ==> #[trigger] grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < m && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
                0 <= j <= n,
                ops as int == Self::total_ops_cols(grid@, j as int),
                0 <= ops as int <= (j as int) * 250_000,
            decreases n - j,
        {
            let ghost j_old: int = j as int;
            let mut prev: i32 = grid[0][j];
            let mut col_ops: i64 = 0;
            let mut i: usize = 1;
            proof {
                assert(Self::adjusted_col_val(grid@, 0, j_old) == grid@[0][j_old] as int);
                assert(Self::col_ops_prefix(grid@, 0, j_old) == 0);
            }
            while i < m
                invariant
                    m == grid.len(),
                    n == grid[0].len(),
                    1 <= m <= 50,
                    1 <= n <= 50,
                    forall |r: int| 0 <= r < m ==> #[trigger] grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < m && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
                    0 <= j_old < n,
                    j as int == j_old,
                    1 <= i <= m,
                    prev as int == Self::adjusted_col_val(grid@, i as int - 1, j_old),
                    col_ops as int == Self::col_ops_prefix(grid@, i as int - 1, j_old),
                    0 <= prev as int <= 2499 + (i as int - 1),
                    0 <= col_ops as int <= (i as int - 1) * 2550,
                decreases m - i,
            {
                let ghost i_old: int = i as int;
                let ghost col_old: int = col_ops as int;
                proof {
                    assert(i < m);
                    assert(j < grid[i as int].len());
                }
                let current = grid[i][j];
                let target = if current <= prev { prev + 1 } else { current };
                let inc = target - current;
                proof {
                    assert(Self::adjusted_col_val(grid@, i_old, j_old) == {
                        let p = Self::adjusted_col_val(grid@, i_old - 1, j_old);
                        if (grid@[i_old][j_old] as int) <= p { p + 1 } else { grid@[i_old][j_old] as int }
                    });
                    if current <= prev {
                        assert(grid@[i_old][j_old] as int <= Self::adjusted_col_val(grid@, i_old - 1, j_old));
                        assert(target as int == Self::adjusted_col_val(grid@, i_old, j_old));
                        assert(inc as int == prev as int + 1 - current as int);
                        assert(0 <= inc as int <= 2550) by (nonlinear_arith)
                            requires
                                0 <= current as int,
                                current as int <= prev as int,
                                prev as int <= 2499 + (i_old - 1),
                                i_old <= 49,
                                inc as int == prev as int + 1 - current as int,
                        {};
                    } else {
                        assert(Self::adjusted_col_val(grid@, i_old - 1, j_old) < grid@[i_old][j_old] as int);
                        assert(target as int == Self::adjusted_col_val(grid@, i_old, j_old));
                        assert(inc == 0);
                        assert(0 <= inc as int <= 2550);
                    }
                    assert(Self::col_ops_prefix(grid@, i_old, j_old) ==
                        Self::col_ops_prefix(grid@, i_old - 1, j_old)
                            + (Self::adjusted_col_val(grid@, i_old, j_old) - grid@[i_old][j_old] as int));
                    assert(inc as int == Self::adjusted_col_val(grid@, i_old, j_old) - grid@[i_old][j_old] as int);
                }
                col_ops = col_ops + inc as i64;
                prev = target;
                i += 1;
                proof {
                    assert(i as int == i_old + 1);
                    assert(col_ops as int == col_old + inc as int);
                    assert(col_ops as int == Self::col_ops_prefix(grid@, i_old, j_old));
                    assert(prev as int == Self::adjusted_col_val(grid@, i_old, j_old));
                    assert(0 <= prev as int <= 2499 + (i as int - 1));
                    assert(0 <= col_ops as int <= (i_old - 1) * 2550 + 2550) by (nonlinear_arith)
                        requires
                            0 <= col_old,
                            col_old <= (i_old - 1) * 2550,
                            0 <= inc as int <= 2550,
                            col_ops as int == col_old + inc as int,
                    {};
                    assert((i_old - 1) * 2550 + 2550 == (i as int - 1) * 2550);
                }
            }
            proof {
                assert(i == m);
                assert(col_ops as int == Self::col_ops_prefix(grid@, m as int - 1, j_old));
                assert(col_ops as int <= (m as int - 1) * 2550);
                assert((m as int - 1) * 2550 <= 250_000) by (nonlinear_arith)
                    requires
                        1 <= m <= 50,
                {};
                assert(col_ops as int <= 250_000);
            }
            let ghost ops_old: int = ops as int;
            ops = ops + col_ops;
            proof {
                assert(ops as int == ops_old + col_ops as int);
                assert(Self::total_ops_cols(grid@, j_old + 1) ==
                    Self::total_ops_cols(grid@, j_old) + Self::col_ops_prefix(grid@, m as int - 1, j_old));
                assert(ops as int == Self::total_ops_cols(grid@, j_old + 1));
                assert(ops as int <= (j_old + 1) * 250_000) by (nonlinear_arith)
                    requires
                        ops_old <= j_old * 250_000,
                        col_ops as int <= 250_000,
                        ops as int == ops_old + col_ops as int,
                {};
            }
            j += 1;
            proof {
                assert(j as int == j_old + 1);
                assert(ops as int == Self::total_ops_cols(grid@, j as int));
                assert(0 <= ops as int <= (j as int) * 250_000);
            }
        }
        proof {
            assert(j == n);
            assert(ops as int == Self::total_ops_cols(grid@, n as int));
            assert((n as int) * 250_000 <= 2_147_483_647) by (nonlinear_arith)
                requires
                    n <= 50,
            {};
            assert(ops as int <= 2_147_483_647) by (nonlinear_arith)
                requires
                    ops as int <= (n as int) * 250_000,
                    (n as int) * 250_000 <= 2_147_483_647,
            {};
            assert(0 <= ops as int);
            assert((ops as i32) as int == ops as int);
        }
        ops as i32
    }
}

} 
