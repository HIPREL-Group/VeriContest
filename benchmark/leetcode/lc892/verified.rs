use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn cell_contrib(grid: Seq<Vec<i32>>, i: int, j: int, n: int) -> int
        recommends
            0 <= i < n,
            0 <= j < n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        let v = grid[i][j] as int;
        let base = if v > 0 { 4 * v + 2 } else { 0 };
        let up = if i > 0 { 2 * Self::spec_min(v, grid[i - 1][j] as int) } else { 0 };
        let left = if j > 0 { 2 * Self::spec_min(v, grid[i][j - 1] as int) } else { 0 };
        base - up - left
    }

    pub open spec fn row_sum(grid: Seq<Vec<i32>>, n: int, row: int, col_end: int) -> int
        recommends
            0 <= row < n,
            0 <= col_end <= n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases col_end,
    {
        if col_end <= 0 {
            0
        } else {
            Self::row_sum(grid, n, row, col_end - 1) + Self::cell_contrib(grid, row, col_end - 1, n)
        }
    }

    pub open spec fn surface_area_spec(grid: Seq<Vec<i32>>, n: int, row_end: int) -> int
        recommends
            0 <= row_end <= n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        decreases row_end,
    {
        if row_end <= 0 {
            0
        } else {
            Self::surface_area_spec(grid, n, row_end - 1) + Self::row_sum(grid, n, row_end - 1, n)
        }
    }

    pub open spec fn surface_area_total(grid: Seq<Vec<i32>>, n: int) -> int
        recommends
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
    {
        Self::surface_area_spec(grid, n, n)
    }

    proof fn lemma_cell_contrib_nonneg(grid: Seq<Vec<i32>>, i: int, j: int, n: int)
        requires
            0 <= i < n,
            0 <= j < n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid.len() ==> 0 <= #[trigger] grid[r][c] <= 50,
        ensures
            0 <= Self::cell_contrib(grid, i, j, n),
    {
        reveal(Solution::cell_contrib);
        assert(Self::spec_min(grid[i][j] as int, grid[i][j] as int) == grid[i][j] as int);
    }

    proof fn lemma_row_sum_full(grid: Seq<Vec<i32>>, n: int, row: int)
        requires
            0 <= row < n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        ensures
            Self::surface_area_spec(grid, n, row + 1) == Self::surface_area_spec(grid, n, row)
                + Self::row_sum(grid, n, row, n),
        decreases n - row,
    {
        reveal_with_fuel(Solution::surface_area_spec, 2);
        reveal_with_fuel(Solution::row_sum, 1);
    }

    proof fn lemma_cell_contrib_bounded(grid: Seq<Vec<i32>>, i: int, j: int, n: int)
        requires
            0 <= i < n,
            0 <= j < n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid.len() ==> 0 <= #[trigger] grid[r][c] <= 50,
        ensures
            Self::cell_contrib(grid, i, j, n) <= 202,
        decreases 0int,
    {
        reveal(Solution::cell_contrib);
    }

    proof fn lemma_surface_area_bounded(grid: Seq<Vec<i32>>, n: int, row_end: int)
        requires
            0 <= row_end <= n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid.len() ==> 0 <= #[trigger] grid[r][c] <= 50,
        ensures
            Self::surface_area_spec(grid, n, row_end) <= 202 * row_end * n,
        decreases row_end,
    {
        if row_end > 0 {
            Self::lemma_surface_area_bounded(grid, n, row_end - 1);
            Self::lemma_row_sum_bounded(grid, n, row_end - 1, n);
            reveal_with_fuel(Solution::surface_area_spec, 2);
            reveal_with_fuel(Solution::row_sum, 1);
            assert(Self::surface_area_spec(grid, n, row_end) <= 202 * row_end * n) by (nonlinear_arith)
                requires
                    Self::surface_area_spec(grid, n, row_end - 1) <= 202 * (row_end - 1) * n,
                    Self::row_sum(grid, n, row_end - 1, n) <= 202 * n,
                    Self::surface_area_spec(grid, n, row_end)
                        == Self::surface_area_spec(grid, n, row_end - 1)
                            + Self::row_sum(grid, n, row_end - 1, n);
        }
    }

    proof fn lemma_row_sum_bounded(grid: Seq<Vec<i32>>, n: int, row: int, col_end: int)
        requires
            0 <= row < n,
            0 <= col_end <= n,
            0 <= n <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid.len() ==> 0 <= #[trigger] grid[r][c] <= 50,
        ensures
            Self::row_sum(grid, n, row, col_end) <= 202 * col_end,
        decreases col_end,
    {
        if col_end > 0 {
            Self::lemma_row_sum_bounded(grid, n, row, col_end - 1);
            Self::lemma_cell_contrib_bounded(grid, row, col_end - 1, n);
            reveal_with_fuel(Solution::row_sum, 2);
            assert(Self::row_sum(grid, n, row, col_end) <= 202 * col_end) by (nonlinear_arith)
                requires
                    Self::row_sum(grid, n, row, col_end - 1) <= 202 * (col_end - 1),
                    Self::cell_contrib(grid, row, col_end - 1, n) <= 202,
                    Self::row_sum(grid, n, row, col_end)
                        == Self::row_sum(grid, n, row, col_end - 1)
                            + Self::cell_contrib(grid, row, col_end - 1, n);
        }
    }

    pub fn surface_area(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 50,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
        ensures
            result as int == Self::surface_area_total(grid@, grid.len() as int),
    {
        let n = grid.len();
        let mut res: i32 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                n == grid.len(),
                1 <= n <= 50,
                0 <= i <= n,
                forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
                forall |r: int, c: int|
                    0 <= r < grid.len() && 0 <= c < grid.len() ==> 0 <= #[trigger] grid[r][c] <= 50,
                res as int == Self::surface_area_spec(grid@, n as int, i as int),
                0 <= res as int <= 202 * (n as int) * (n as int),
            decreases n - i,
        {
            proof {
                Self::lemma_surface_area_bounded(grid@, n as int, i as int);
            }
            let mut j: usize = 0;

            while j < n
                invariant
                    n == grid.len(),
                    1 <= n <= 50,
                    i < n,
                    0 <= j <= n,
                    forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
                    forall |r: int, c: int|
                        0 <= r < grid.len() && 0 <= c < grid.len() ==> 0 <= #[trigger] grid[r][c] <= 50,
                    res as int == Self::surface_area_spec(grid@, n as int, i as int)
                        + Self::row_sum(grid@, n as int, i as int, j as int),
                    0 <= res as int,
                    res as int <= 202 * (n as int) * (n as int),
                decreases n - j,
            {
                proof {
                    assert((i as int) < grid.len() as int);
                    assert(grid[i as int].len() == grid.len());
                    assert((j as int) < n as int);
                    assert((j as int) < grid[i as int].len());
                }
                if grid[i][j] > 0 {
                    proof {
                        assert(202 * 50 * 50 <= 2147483647) by (nonlinear_arith);
                        assert((n as int) <= 50);
                        assert(202 * (n as int) * (n as int) <= 2147483647) by (nonlinear_arith)
                            requires (n as int) <= 50, 202 * 50 * 50 <= 2147483647;
                        assert(res as int + (grid@[i as int][j as int] as int) * 4 + 2 <= 202 * (n as int) * (n as int) + 202)
                            by (nonlinear_arith)
                            requires
                                res as int <= 202 * (n as int) * (n as int),
                                (grid@[i as int][j as int] as int) <= 50;
                        assert(202 * (n as int) * (n as int) + 202 <= 2147483647) by (nonlinear_arith)
                            requires 202 * (n as int) * (n as int) <= 2147483647;
                        assert(res as int + (grid@[i as int][j as int] as int) * 4 + 2 <= 2147483647) by (nonlinear_arith)
                            requires
                                res as int + (grid@[i as int][j as int] as int) * 4 + 2 <= 202 * (n as int) * (n as int) + 202,
                                202 * (n as int) * (n as int) + 202 <= 2147483647;
                    }
                    res = res + grid[i][j] * 4 + 2;
                }
                if i > 0 {
                    proof {
                        assert((i as int - 1) >= 0);
                        assert((i as int - 1) < grid@.len());
                        assert(grid@[i as int - 1].len() == grid@.len());
                        assert((j as int) < grid@[i as int - 1].len());
                    }
                    let a = grid[i][j];
                    let b = grid[i - 1][j];
                    let m = if a <= b { a } else { b };
                    proof {
                        assert(res as int >= 2 * (m as int));
                    }
                    res = res - m * 2;
                }
                if j > 0 {
                    proof {
                        assert((j as int - 1) >= 0);
                        assert((j as int - 1) < grid@[i as int].len());
                    }
                    let a = grid[i][j];
                    let b = grid[i][j - 1];
                    let m = if a <= b { a } else { b };
                    proof {
                        assert(res as int >= 2 * (m as int));
                    }
                    res = res - m * 2;
                }
                proof {
                    Self::lemma_surface_area_bounded(grid@, n as int, i as int);
                    Self::lemma_row_sum_bounded(grid@, n as int, i as int, (j as int) + 1);
                    assert((i as int) * (n as int) + (j as int) + 1 <= (n as int) * (n as int))
                        by (nonlinear_arith) requires (i as int) < (n as int), (j as int) < (n as int);
                    assert(res as int <= 202 * (n as int) * (n as int)) by (nonlinear_arith)
                        requires
                            res as int == Self::surface_area_spec(grid@, n as int, i as int)
                                + Self::row_sum(grid@, n as int, i as int, (j as int) + 1),
                            Self::surface_area_spec(grid@, n as int, i as int) <= 202 * (i as int) * (n as int),
                            Self::row_sum(grid@, n as int, i as int, (j as int) + 1) <= 202 * ((j as int) + 1),
                            (i as int) * (n as int) + (j as int) + 1 <= (n as int) * (n as int);
                }
                j += 1;
            }

            proof {
                Self::lemma_row_sum_full(grid@, n as int, i as int);
                Self::lemma_surface_area_bounded(grid@, n as int, (i as int) + 1);
                assert((i as int) + 1 <= n as int);
                assert(202 * ((i as int) + 1) * (n as int) <= 202 * (n as int) * (n as int))
                    by (nonlinear_arith) requires (i as int) + 1 <= n as int;
                assert(res as int <= 202 * (n as int) * (n as int));
            }
            i += 1;
        }

        res
    }
}

}
