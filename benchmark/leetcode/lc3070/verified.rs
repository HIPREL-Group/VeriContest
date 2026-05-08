use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn col_sum(grid: Seq<Vec<i32>>, rows: int, c: int) -> int
        decreases rows,
    {
        if rows <= 0 {
            0
        } else {
            Self::col_sum(grid, rows - 1, c) + grid[rows - 1][c] as int
        }
    }

    pub open spec fn rect_sum(grid: Seq<Vec<i32>>, rows: int, cols: int) -> int
        decreases cols,
    {
        if rows <= 0 || cols <= 0 {
            0
        } else {
            Self::rect_sum(grid, rows, cols - 1) + Self::col_sum(grid, rows, cols - 1)
        }
    }

    pub open spec fn row_count(grid: Seq<Vec<i32>>, k: int, r: int, cols: int) -> int
        decreases cols,
    {
        if cols <= 0 {
            0
        } else {
            Self::row_count(grid, k, r, cols - 1)
                + if Self::rect_sum(grid, r + 1, cols) <= k { 1int } else { 0int }
        }
    }

    pub open spec fn total_count(grid: Seq<Vec<i32>>, k: int, rows: int) -> int
        decreases rows,
    {
        if rows <= 0 {
            0
        } else {
            Self::total_count(grid, k, rows - 1)
                + Self::row_count(grid, k, rows - 1, grid[0].len() as int)
        }
    }

    pub open spec fn count_submatrices_spec(grid: Seq<Vec<i32>>, k: int) -> int {
        Self::total_count(grid, k, grid.len() as int)
    }

    pub open spec fn area_cols(rows: int, cols: int) -> int
        decreases cols,
    {
        if rows <= 0 || cols <= 0 {
            0
        } else {
            Self::area_cols(rows, cols - 1) + rows
        }
    }

    pub open spec fn area_rows(rows: int, cols: int) -> int
        decreases rows,
    {
        if rows <= 0 || cols <= 0 {
            0
        } else {
            Self::area_rows(rows - 1, cols) + cols
        }
    }

    proof fn lemma_cmp_i64_i32(x: i64, y: i32)
        requires
            0 <= x <= 1_000_000_000,
            1 <= y <= 1_000_000_000,
        ensures
            (x <= y as i64) <==> (x as int <= y as int),
    {
    }

    proof fn lemma_area_cols_bound(rows: int, cols: int)
        requires
            0 <= rows <= 1000,
            0 <= cols <= 1000,
        ensures
            0 <= Self::area_cols(rows, cols),
            Self::area_cols(rows, cols) <= 1000 * cols,
            Self::area_cols(rows, cols) <= 1_000_000,
        decreases cols,
    {
        if rows <= 0 || cols <= 0 {
        } else {
            Self::lemma_area_cols_bound(rows, cols - 1);
            assert(Self::area_cols(rows, cols) == Self::area_cols(rows, cols - 1) + rows);
            assert(Self::area_cols(rows, cols - 1) <= 1000 * (cols - 1));
            assert(rows <= 1000);
            assert(1000 * (cols - 1) + rows <= 1000 * cols);
        }
    }

    proof fn lemma_area_rows_bound(rows: int, cols: int)
        requires
            0 <= rows <= 1000,
            0 <= cols <= 1000,
        ensures
            0 <= Self::area_rows(rows, cols),
            Self::area_rows(rows, cols) <= 1000 * rows,
            Self::area_rows(rows, cols) <= 1_000_000,
        decreases rows,
    {
        if rows <= 0 || cols <= 0 {
        } else {
            Self::lemma_area_rows_bound(rows - 1, cols);
            assert(Self::area_rows(rows, cols) == Self::area_rows(rows - 1, cols) + cols);
            assert(Self::area_rows(rows - 1, cols) <= 1000 * (rows - 1));
            assert(cols <= 1000);
            assert(1000 * (rows - 1) + cols <= 1000 * rows);
        }
    }

    proof fn lemma_col_sum_bound(grid: Seq<Vec<i32>>, rows: int, c: int)
        requires
            0 < grid.len() <= 1000,
            0 < grid[0].len() <= 1000,
            0 <= rows <= grid.len(),
            0 <= c < grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, j: int| 0 <= r < grid.len() && 0 <= j < grid[r].len() ==> 0 <= #[trigger] grid[r][j] <= 1000,
        ensures
            0 <= Self::col_sum(grid, rows, c),
            Self::col_sum(grid, rows, c) <= 1000 * rows,
            Self::col_sum(grid, rows, c) <= 1_000_000,
        decreases rows,
    {
        if rows <= 0 {
        } else {
            Self::lemma_col_sum_bound(grid, rows - 1, c);
            assert(Self::col_sum(grid, rows, c) == Self::col_sum(grid, rows - 1, c) + grid[rows - 1][c] as int);
            assert(Self::col_sum(grid, rows - 1, c) <= 1000 * (rows - 1));
            assert(0 <= grid[rows - 1][c] <= 1000);
            assert(1000 * (rows - 1) + grid[rows - 1][c] as int <= 1000 * rows);
        }
    }

    proof fn lemma_rect_sum_bound(grid: Seq<Vec<i32>>, rows: int, cols: int)
        requires
            0 < grid.len() <= 1000,
            0 < grid[0].len() <= 1000,
            0 <= rows <= grid.len(),
            0 <= cols <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, j: int| 0 <= r < grid.len() && 0 <= j < grid[r].len() ==> 0 <= #[trigger] grid[r][j] <= 1000,
        ensures
            0 <= Self::rect_sum(grid, rows, cols),
            Self::rect_sum(grid, rows, cols) <= 1000 * Self::area_cols(rows, cols),
            Self::rect_sum(grid, rows, cols) <= 1_000_000_000,
        decreases cols,
    {
        if rows <= 0 || cols <= 0 {
        } else {
            Self::lemma_rect_sum_bound(grid, rows, cols - 1);
            Self::lemma_col_sum_bound(grid, rows, cols - 1);
            Self::lemma_area_cols_bound(rows, cols);
            assert(Self::rect_sum(grid, rows, cols)
                == Self::rect_sum(grid, rows, cols - 1) + Self::col_sum(grid, rows, cols - 1));
            assert(Self::rect_sum(grid, rows, cols - 1) <= 1000 * Self::area_cols(rows, cols - 1));
            assert(Self::col_sum(grid, rows, cols - 1) <= 1000 * rows);
            assert(Self::area_cols(rows, cols) == Self::area_cols(rows, cols - 1) + rows);
            assert(1000 * Self::area_cols(rows, cols - 1) + 1000 * rows
                == 1000 * Self::area_cols(rows, cols));
            assert(Self::rect_sum(grid, rows, cols) <= 1000 * Self::area_cols(rows, cols));
            assert(Self::area_cols(rows, cols) <= 1_000_000);
        }
    }

    proof fn lemma_row_count_bound(grid: Seq<Vec<i32>>, k: int, r: int, cols: int)
        requires
            0 < grid.len(),
            0 < grid[0].len(),
            0 <= r < grid.len(),
            0 <= cols <= grid[0].len(),
        ensures
            0 <= Self::row_count(grid, k, r, cols),
            Self::row_count(grid, k, r, cols) <= cols,
        decreases cols,
    {
        if cols <= 0 {
        } else {
            Self::lemma_row_count_bound(grid, k, r, cols - 1);
            assert(Self::row_count(grid, k, r, cols)
                == Self::row_count(grid, k, r, cols - 1)
                    + if Self::rect_sum(grid, r + 1, cols) <= k { 1int } else { 0int });
        }
    }

    proof fn lemma_total_count_bound(grid: Seq<Vec<i32>>, k: int, rows: int)
        requires
            0 < grid.len() <= 1000,
            0 < grid[0].len() <= 1000,
            0 <= rows <= grid.len(),
        ensures
            0 <= Self::total_count(grid, k, rows),
            Self::total_count(grid, k, rows) <= Self::area_rows(rows, grid[0].len() as int),
            Self::total_count(grid, k, rows) <= 1_000_000,
        decreases rows,
    {
        if rows <= 0 {
        } else {
            Self::lemma_total_count_bound(grid, k, rows - 1);
            Self::lemma_row_count_bound(grid, k, rows - 1, grid[0].len() as int);
            Self::lemma_area_rows_bound(rows, grid[0].len() as int);
            assert(Self::total_count(grid, k, rows)
                == Self::total_count(grid, k, rows - 1)
                    + Self::row_count(grid, k, rows - 1, grid[0].len() as int));
            assert(Self::total_count(grid, k, rows - 1)
                <= Self::area_rows(rows - 1, grid[0].len() as int));
            assert(Self::row_count(grid, k, rows - 1, grid[0].len() as int)
                <= grid[0].len() as int);
            assert(Self::area_rows(rows, grid[0].len() as int)
                == Self::area_rows(rows - 1, grid[0].len() as int) + grid[0].len() as int);
            assert(Self::total_count(grid, k, rows)
                <= Self::area_rows(rows, grid[0].len() as int));
            assert(Self::area_rows(rows, grid[0].len() as int) <= 1_000_000);
        }
    }

    pub fn count_submatrices(grid: Vec<Vec<i32>>, k: i32) -> (result: i32)
        requires
            1 <= grid.len() <= 1000,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            1 <= grid[0].len() <= 1000,
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 1000,
            1 <= k <= 1_000_000_000,
        ensures
            result as int == Self::count_submatrices_spec(grid@, k as int),
    {
        let m = grid.len();
        let n = grid[0].len();

        let mut cols: Vec<i64> = Vec::new();
        let mut t: usize = 0;
        while t < n
            invariant
                n == grid[0].len(),
                1 <= n <= 1000,
                0 <= t <= n,
                cols.len() == t,
                forall |c: int| 0 <= c < t ==> #[trigger] cols[c] == 0,
            decreases n - t,
        {
            cols.push(0);
            t = t + 1;
        }

        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let k64 = k as i64;
        while i < m
            invariant
                m == grid.len(),
                n == grid[0].len(),
                1 <= m <= 1000,
                1 <= n <= 1000,
                forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < n ==> 0 <= #[trigger] grid[r][c] <= 1000,
                1 <= k <= 1_000_000_000,
                0 <= i <= m,
                k64 == k as i64,
                cols.len() == n,
                forall |c: int| 0 <= c < n ==> #[trigger] cols[c] as int == Self::col_sum(grid@, i as int, c),
                forall |c: int| 0 <= c < n ==> 0 <= #[trigger] cols[c] <= 1_000_000,
                ans as int == Self::total_count(grid@, k as int, i as int),
                0 <= ans <= 1_000_000,
            decreases m - i,
        {
            let mut row_prefix: i64 = 0;
            let mut j: usize = 0;
            while j < n
                invariant
                    m == grid.len(),
                    n == grid[0].len(),
                    1 <= m <= 1000,
                    1 <= n <= 1000,
                    forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < n ==> 0 <= #[trigger] grid[r][c] <= 1000,
                    1 <= k <= 1_000_000_000,
                    0 <= i < m,
                    0 <= j <= n,
                    k64 == k as i64,
                    cols.len() == n,
                    forall |c: int| 0 <= c < j ==> #[trigger] cols[c] as int == Self::col_sum(grid@, i as int + 1, c),
                    forall |c: int| j <= c < n ==> #[trigger] cols[c] as int == Self::col_sum(grid@, i as int, c),
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] cols[c] <= 1_000_000,
                    forall |c: int| j <= c < n ==> 0 <= #[trigger] cols[c] <= 1_000_000,
                    row_prefix as int == Self::rect_sum(grid@, i as int + 1, j as int),
                    0 <= row_prefix <= 1_000_000_000,
                    ans as int
                        == Self::total_count(grid@, k as int, i as int)
                            + Self::row_count(grid@, k as int, i as int, j as int),
                    0 <= ans <= 1_000_000,
                decreases n - j,
            {
                let ghost j_old = j as int;
                let ghost ans_old = ans as int;
                let ghost cols_before = cols@;

                proof {
                    assert(i < m);
                    assert(j < n);
                    assert(grid[i as int].len() == n);
                    assert((j as int) < grid[i as int].len());
                }

                let old_col = cols[j];
                let new_col = old_col + grid[i][j] as i64;
                cols.set(j, new_col);
                row_prefix = row_prefix + new_col;

                if row_prefix <= k64 {
                    ans = ans + 1;
                }

                proof {
                    assert(old_col as int == Self::col_sum(grid@, i as int, j_old));
                    assert(Self::col_sum(grid@, i as int + 1, j_old)
                        == Self::col_sum(grid@, i as int, j_old) + grid@[i as int][j_old] as int);
                    assert(new_col as int == Self::col_sum(grid@, i as int + 1, j_old));

                    assert(Self::rect_sum(grid@, i as int + 1, j_old + 1)
                        == Self::rect_sum(grid@, i as int + 1, j_old)
                            + Self::col_sum(grid@, i as int + 1, j_old));
                    assert(row_prefix as int == Self::rect_sum(grid@, i as int + 1, j_old + 1));

                    assert(Self::row_count(grid@, k as int, i as int, j_old + 1)
                        == Self::row_count(grid@, k as int, i as int, j_old)
                            + if Self::rect_sum(grid@, i as int + 1, j_old + 1) <= k as int { 1int } else { 0int });

                    Self::lemma_rect_sum_bound(grid@, i as int + 1, j_old + 1);
                    assert(0 <= row_prefix <= 1_000_000_000);
                    Self::lemma_cmp_i64_i32(row_prefix, k);
                    assert(k64 == k as i64);
                    assert((row_prefix <= k64) <==> (row_prefix as int <= k as int));
                    if row_prefix <= k64 {
                        assert(row_prefix as int <= k as int);
                        assert(ans as int == ans_old + 1);
                    } else {
                        assert(!(row_prefix as int <= k as int));
                        assert(ans as int == ans_old);
                    }

                    assert(ans as int
                        == Self::total_count(grid@, k as int, i as int)
                            + Self::row_count(grid@, k as int, i as int, j_old + 1));

                    assert forall |c: int| 0 <= c < j_old + 1 implies cols[c] as int == Self::col_sum(grid@, i as int + 1, c) by {
                        if c < j_old {
                            assert(cols[c] == cols_before[c]);
                        } else {
                            assert(c == j_old);
                        }
                    }

                    assert forall |c: int| j_old + 1 <= c < n implies cols[c] as int == Self::col_sum(grid@, i as int, c) by {
                        assert(cols[c] == cols_before[c]);
                    }

                    assert forall |c: int| 0 <= c < j_old + 1 implies 0 <= #[trigger] cols[c] <= 1_000_000 by {
                        if c < j_old {
                            assert(cols[c] == cols_before[c]);
                        } else {
                            assert(c == j_old);
                            Self::lemma_col_sum_bound(grid@, i as int + 1, j_old);
                            assert(cols[j_old] as int == Self::col_sum(grid@, i as int + 1, j_old));
                            assert(0 <= cols[j_old] <= 1_000_000);
                            assert(cols[c] == cols[j_old]);
                        }
                    }

                    assert forall |c: int| j_old + 1 <= c < n implies 0 <= #[trigger] cols[c] <= 1_000_000 by {
                        assert(cols[c] == cols_before[c]);
                    }

                    Self::lemma_total_count_bound(grid@, k as int, i as int);
                    Self::lemma_row_count_bound(grid@, k as int, i as int, j_old + 1);
                    Self::lemma_area_rows_bound(i as int, n as int);
                    assert(Self::total_count(grid@, k as int, i as int) <= Self::area_rows(i as int, n as int));
                    assert(Self::row_count(grid@, k as int, i as int, j_old + 1) <= j_old + 1);
                    assert(j_old + 1 <= n as int);
                    assert(ans as int <= Self::area_rows(i as int, n as int) + n as int);
                    assert(Self::area_rows(i as int, n as int) <= 1000 * i as int);
                    assert(i < m);
                    assert(m <= 1000);
                    assert(i as int <= 999);
                    assert(1000 * i as int + n as int <= 1_000_000);
                    assert(0 <= ans <= 1_000_000);
                }

                j = j + 1;
            }

            proof {
                assert(j == n);
                assert(Self::total_count(grid@, k as int, i as int + 1)
                    == Self::total_count(grid@, k as int, i as int)
                        + Self::row_count(grid@, k as int, i as int, n as int));
                assert(ans as int == Self::total_count(grid@, k as int, i as int + 1));
                assert forall |c: int| 0 <= c < n implies cols[c] as int == Self::col_sum(grid@, i as int + 1, c) by {
                }
                Self::lemma_total_count_bound(grid@, k as int, i as int + 1);
                assert(0 <= ans <= 1_000_000);
            }

            i = i + 1;
        }

        proof {
            assert(i == m);
            assert(ans as int == Self::count_submatrices_spec(grid@, k as int));
            Self::lemma_total_count_bound(grid@, k as int, m as int);
            assert(0 <= ans <= 1_000_000);
        }

        ans as i32
    }
}

}
