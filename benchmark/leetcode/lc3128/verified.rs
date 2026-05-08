use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_ones_prefix(grid: Seq<Vec<i32>>, row: int, upto: int) -> int
        recommends
            grid.len() > 0,
            0 <= row < grid.len(),
            0 <= upto <= grid[row].len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::row_ones_prefix(grid, row, upto - 1)
                + if grid[row][upto - 1] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn row_ones(grid: Seq<Vec<i32>>, row: int) -> int
        recommends
            grid.len() > 0,
            0 <= row < grid.len(),
    {
        Self::row_ones_prefix(grid, row, grid[row].len() as int)
    }

    pub open spec fn col_ones_prefix(grid: Seq<Vec<i32>>, col: int, upto: int) -> int
        recommends
            grid.len() > 0,
            0 <= col < grid[0].len(),
            0 <= upto <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::col_ones_prefix(grid, col, upto - 1)
                + if grid[upto - 1][col] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn col_ones(grid: Seq<Vec<i32>>, col: int) -> int
        recommends
            grid.len() > 0,
            0 <= col < grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        Self::col_ones_prefix(grid, col, grid.len() as int)
    }

    pub open spec fn triangle_at(grid: Seq<Vec<i32>>, row: int, col: int) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            0 <= row < grid.len(),
            0 <= col < grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        if grid[row][col] == 1 {
            (Self::row_ones(grid, row) - 1) * (Self::col_ones(grid, col) - 1)
        } else {
            0
        }
    }

    pub open spec fn row_triangle_sum_prefix(grid: Seq<Vec<i32>>, row: int, upto: int) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            0 <= row < grid.len(),
            0 <= upto <= grid[0].len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::row_triangle_sum_prefix(grid, row, upto - 1)
                + Self::triangle_at(grid, row, upto - 1)
        }
    }

    pub open spec fn total_triangle_sum_prefix(grid: Seq<Vec<i32>>, upto_rows: int) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            0 <= upto_rows <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        decreases upto_rows,
    {
        if upto_rows <= 0 {
            0
        } else {
            Self::total_triangle_sum_prefix(grid, upto_rows - 1)
                + Self::row_triangle_sum_prefix(grid, upto_rows - 1, grid[0].len() as int)
        }
    }

    pub open spec fn right_triangles_spec(grid: Seq<Vec<i32>>) -> int
        recommends
            grid.len() > 0,
            grid[0].len() > 0,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
    {
        Self::total_triangle_sum_prefix(grid, grid.len() as int)
    }

    proof fn lemma_row_ones_prefix_bounds(grid: Seq<Vec<i32>>, row: int, upto: int)
        requires
            grid.len() > 0,
            0 <= row < grid.len(),
            0 <= upto <= grid[row].len(),
            forall |c: int| 0 <= c < grid[row].len() ==> {
                let v = #[trigger] grid[row][c];
                v == 0 || v == 1
            },
        ensures
            0 <= Self::row_ones_prefix(grid, row, upto) <= upto,
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_row_ones_prefix_bounds(grid, row, upto - 1);
            assert(grid[row][upto - 1] == 0 || grid[row][upto - 1] == 1);
        }
    }

    proof fn lemma_col_ones_prefix_bounds(grid: Seq<Vec<i32>>, col: int, upto: int)
        requires
            grid.len() > 0,
            0 <= col < grid[0].len(),
            0 <= upto <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> {
                let v = #[trigger] grid[r][c];
                v == 0 || v == 1
            },
        ensures
            0 <= Self::col_ones_prefix(grid, col, upto) <= upto,
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_col_ones_prefix_bounds(grid, col, upto - 1);
            assert(grid[upto - 1][col] == 0 || grid[upto - 1][col] == 1);
        }
    }

    proof fn lemma_row_ones_ge_one_at(grid: Seq<Vec<i32>>, row: int, col: int, upto: int)
        requires
            grid.len() > 0,
            0 <= row < grid.len(),
            0 <= col < upto <= grid[row].len(),
            grid[row][col] == 1,
            forall |c: int| 0 <= c < grid[row].len() ==> {
                let v = #[trigger] grid[row][c];
                v == 0 || v == 1
            },
        ensures
            Self::row_ones_prefix(grid, row, upto) >= 1,
        decreases upto,
    {
        if upto - 1 == col {
            Self::lemma_row_ones_prefix_bounds(grid, row, upto - 1);
            assert(grid[row][upto - 1] == 1);
            assert(Self::row_ones_prefix(grid, row, upto)
                == Self::row_ones_prefix(grid, row, upto - 1) + 1);
        } else {
            assert(col < upto - 1);
            Self::lemma_row_ones_ge_one_at(grid, row, col, upto - 1);
            assert(Self::row_ones_prefix(grid, row, upto)
                == Self::row_ones_prefix(grid, row, upto - 1)
                    + if grid[row][upto - 1] == 1 { 1int } else { 0int });
            assert(0 <= if grid[row][upto - 1] == 1 { 1int } else { 0int });
        }
    }

    proof fn lemma_col_ones_ge_one_at(grid: Seq<Vec<i32>>, col: int, row: int, upto: int)
        requires
            grid.len() > 0,
            0 <= col < grid[0].len(),
            0 <= row < upto <= grid.len(),
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            grid[row][col] == 1,
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> {
                let v = #[trigger] grid[r][c];
                v == 0 || v == 1
            },
        ensures
            Self::col_ones_prefix(grid, col, upto) >= 1,
        decreases upto,
    {
        if upto - 1 == row {
            Self::lemma_col_ones_prefix_bounds(grid, col, upto - 1);
            assert(grid[upto - 1][col] == 1);
            assert(Self::col_ones_prefix(grid, col, upto)
                == Self::col_ones_prefix(grid, col, upto - 1) + 1);
        } else {
            assert(row < upto - 1);
            Self::lemma_col_ones_ge_one_at(grid, col, row, upto - 1);
            assert(Self::col_ones_prefix(grid, col, upto)
                == Self::col_ones_prefix(grid, col, upto - 1)
                    + if grid[upto - 1][col] == 1 { 1int } else { 0int });
            assert(0 <= if grid[upto - 1][col] == 1 { 1int } else { 0int });
        }
    }

    pub fn number_of_right_triangles(grid: Vec<Vec<i32>>) -> (result: i64)
        requires
            1 <= grid.len() <= 1000,
            1 <= grid[0].len() <= 1000,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> {
                let v = #[trigger] grid[r][c];
                v == 0 || v == 1
            },
        ensures
            result as int == Self::right_triangles_spec(grid@),
    {
        let m = grid.len();
        let n = grid[0].len();

        let mut row_counts: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                1 <= m <= 1000,
                1 <= n <= 1000,
                m == grid.len(),
                n == grid[0].len(),
                forall |r: int| 0 <= r < m as int ==> #[trigger] grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < m as int && 0 <= c < grid[r].len() ==> {
                    let v = #[trigger] grid[r][c];
                    v == 0 || v == 1
                },
                0 <= i <= m,
                row_counts.len() == i,
                forall |r: int| 0 <= r < i as int ==> #[trigger] row_counts[r] as int == Self::row_ones(grid@, r),
                forall |r: int| 0 <= r < i as int ==> 0 <= #[trigger] row_counts[r] <= n as i64,
            decreases m - i,
        {
            let mut row_sum: i64 = 0;
            let mut j: usize = 0;
            while j < n
                invariant
                    1 <= m <= 1000,
                    1 <= n <= 1000,
                    m == grid.len(),
                    n == grid[0].len(),
                    0 <= i < m,
                    forall |r: int| 0 <= r < m as int ==> #[trigger] grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < m as int && 0 <= c < grid[r].len() ==> {
                        let v = #[trigger] grid[r][c];
                        v == 0 || v == 1
                    },
                    0 <= j <= n,
                    grid[i as int].len() == n,
                    row_sum as int == Self::row_ones_prefix(grid@, i as int, j as int),
                    0 <= row_sum <= j as i64,
                decreases n - j,
            {
                if grid[i][j] == 1 {
                    row_sum = row_sum + 1;
                }
                proof {
                    assert(Self::row_ones_prefix(grid@, i as int, j as int + 1)
                        == Self::row_ones_prefix(grid@, i as int, j as int)
                            + if grid[i as int][j as int] == 1 { 1int } else { 0int });
                }
                j = j + 1;
            }
            proof {
                assert(j == n);
                assert(row_sum as int == Self::row_ones(grid@, i as int));
                Self::lemma_row_ones_prefix_bounds(grid@, i as int, n as int);
                assert(0 <= row_sum <= n as i64);
            }
            let ghost old_row_counts = row_counts@;
            let ghost old_i = i as int;
            row_counts.push(row_sum);
            proof {
                assert(row_counts@ == old_row_counts.push(row_sum));
                assert(forall |r: int| 0 <= r < old_i ==> #[trigger] row_counts[r] as int == Self::row_ones(grid@, r));
                assert(row_counts[old_i] as int == Self::row_ones(grid@, old_i));
                assert forall |r: int| 0 <= r < old_i + 1 implies #[trigger] row_counts[r] as int == Self::row_ones(grid@, r) by {
                    if r < old_i {
                        assert(row_counts[r] == old_row_counts[r]);
                    } else {
                        assert(r == old_i);
                    }
                };
                assert forall |r: int| 0 <= r < old_i + 1 implies 0 <= #[trigger] row_counts[r] <= n as i64 by {
                    if r < old_i {
                        assert(row_counts[r] == old_row_counts[r]);
                    } else {
                        assert(r == old_i);
                        assert(0 <= row_counts[r] <= n as i64);
                    }
                };
            }
            i = i + 1;
        }

        let mut col_counts: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= m <= 1000,
                1 <= n <= 1000,
                m == grid.len(),
                n == grid[0].len(),
                forall |r: int| 0 <= r < m as int ==> #[trigger] grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < m as int && 0 <= c < grid[r].len() ==> {
                    let v = #[trigger] grid[r][c];
                    v == 0 || v == 1
                },
                row_counts.len() == m,
                forall |r: int| 0 <= r < m as int ==> #[trigger] row_counts[r] as int == Self::row_ones(grid@, r),
                forall |r: int| 0 <= r < m as int ==> 0 <= #[trigger] row_counts[r] <= n as i64,
                0 <= j <= n,
                col_counts.len() == j,
                forall |c: int| 0 <= c < j as int ==> #[trigger] col_counts[c] as int == Self::col_ones(grid@, c),
                forall |c: int| 0 <= c < j as int ==> 0 <= #[trigger] col_counts[c] <= m as i64,
            decreases n - j,
        {
            let mut col_sum: i64 = 0;
            i = 0;
            while i < m
                invariant
                    1 <= m <= 1000,
                    1 <= n <= 1000,
                    m == grid.len(),
                    n == grid[0].len(),
                    0 <= j < n,
                    forall |r: int| 0 <= r < m as int ==> #[trigger] grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < m as int && 0 <= c < grid[r].len() ==> {
                        let v = #[trigger] grid[r][c];
                        v == 0 || v == 1
                    },
                    0 <= i <= m,
                    i < m ==> grid[i as int].len() == n,
                    col_sum as int == Self::col_ones_prefix(grid@, j as int, i as int),
                    0 <= col_sum <= i as i64,
                decreases m - i,
            {
                if grid[i][j] == 1 {
                    col_sum = col_sum + 1;
                }
                proof {
                    assert(Self::col_ones_prefix(grid@, j as int, i as int + 1)
                        == Self::col_ones_prefix(grid@, j as int, i as int)
                            + if grid[i as int][j as int] == 1 { 1int } else { 0int });
                }
                i = i + 1;
            }
            proof {
                assert(i == m);
                assert(col_sum as int == Self::col_ones(grid@, j as int));
                Self::lemma_col_ones_prefix_bounds(grid@, j as int, m as int);
                assert(0 <= col_sum <= m as i64);
            }
            let ghost old_col_counts = col_counts@;
            let ghost old_j = j as int;
            col_counts.push(col_sum);
            proof {
                assert(col_counts@ == old_col_counts.push(col_sum));
                assert(forall |c: int| 0 <= c < old_j ==> #[trigger] col_counts[c] as int == Self::col_ones(grid@, c));
                assert(col_counts[old_j] as int == Self::col_ones(grid@, old_j));
                assert forall |c: int| 0 <= c < old_j + 1 implies #[trigger] col_counts[c] as int == Self::col_ones(grid@, c) by {
                    if c < old_j {
                        assert(col_counts[c] == old_col_counts[c]);
                    } else {
                        assert(c == old_j);
                    }
                };
                assert forall |c: int| 0 <= c < old_j + 1 implies 0 <= #[trigger] col_counts[c] <= m as i64 by {
                    if c < old_j {
                        assert(col_counts[c] == old_col_counts[c]);
                    } else {
                        assert(c == old_j);
                        assert(0 <= col_counts[c] <= m as i64);
                    }
                };
            }
            j = j + 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < m
            invariant
                1 <= m <= 1000,
                1 <= n <= 1000,
                m == grid.len(),
                n == grid[0].len(),
                forall |r: int| 0 <= r < m as int ==> #[trigger] grid[r].len() == n,
                forall |r: int, c: int| 0 <= r < m as int && 0 <= c < grid[r].len() ==> {
                    let v = #[trigger] grid[r][c];
                    v == 0 || v == 1
                },
                row_counts.len() == m,
                forall |r: int| 0 <= r < m as int ==> #[trigger] row_counts[r] as int == Self::row_ones(grid@, r),
                forall |r: int| 0 <= r < m as int ==> 0 <= #[trigger] row_counts[r] <= n as i64,
                col_counts.len() == n,
                forall |c: int| 0 <= c < n as int ==> #[trigger] col_counts[c] as int == Self::col_ones(grid@, c),
                forall |c: int| 0 <= c < n as int ==> 0 <= #[trigger] col_counts[c] <= m as i64,
                0 <= i <= m,
                ans as int == Self::total_triangle_sum_prefix(grid@, i as int),
                0 <= ans as int <= i as int * n as int * 1_000_000,
            decreases m - i,
        {
            j = 0;
            while j < n
                invariant
                    1 <= m <= 1000,
                    1 <= n <= 1000,
                    m == grid.len(),
                    n == grid[0].len(),
                    forall |r: int| 0 <= r < m as int ==> #[trigger] grid[r].len() == n,
                    forall |r: int, c: int| 0 <= r < m as int && 0 <= c < grid[r].len() ==> {
                        let v = #[trigger] grid[r][c];
                        v == 0 || v == 1
                    },
                    row_counts.len() == m,
                    forall |r: int| 0 <= r < m as int ==> #[trigger] row_counts[r] as int == Self::row_ones(grid@, r),
                    forall |r: int| 0 <= r < m as int ==> 0 <= #[trigger] row_counts[r] <= n as i64,
                    col_counts.len() == n,
                    forall |c: int| 0 <= c < n as int ==> #[trigger] col_counts[c] as int == Self::col_ones(grid@, c),
                    forall |c: int| 0 <= c < n as int ==> 0 <= #[trigger] col_counts[c] <= m as i64,
                    0 <= i < m,
                    0 <= j <= n,
                    grid[i as int].len() == n,
                    ans as int == Self::total_triangle_sum_prefix(grid@, i as int)
                        + Self::row_triangle_sum_prefix(grid@, i as int, j as int),
                    0 <= ans as int <= (i as int * n as int + j as int) * 1_000_000,
                decreases n - j,
            {
                let ghost old_ans = ans as int;
                if grid[i][j] == 1 {
                    proof {
                        assert(grid[i as int][j as int] == 1);
                        assert(forall |c: int| 0 <= c < grid[i as int].len() ==> {
                            let v = #[trigger] grid[i as int][c];
                            v == 0 || v == 1
                        });
                        Self::lemma_row_ones_ge_one_at(grid@, i as int, j as int, n as int);
                        Self::lemma_col_ones_ge_one_at(grid@, j as int, i as int, m as int);
                        assert(Self::row_ones(grid@, i as int) == Self::row_ones_prefix(grid@, i as int, n as int));
                        assert(Self::col_ones(grid@, j as int) == Self::col_ones_prefix(grid@, j as int, m as int));
                        assert(1 <= Self::row_ones(grid@, i as int));
                        assert(1 <= Self::col_ones(grid@, j as int));
                        assert(0 <= row_counts[i as int] <= n as i64);
                        assert(0 <= col_counts[j as int] <= m as i64);
                        assert(1 <= row_counts[i as int] as int);
                        assert(1 <= col_counts[j as int] as int);
                        assert(0 <= row_counts[i as int] - 1 <= 999);
                        assert(0 <= col_counts[j as int] - 1 <= 999);
                        assert((row_counts[i as int] - 1) * (col_counts[j as int] - 1) <= 998001)
                            by (nonlinear_arith)
                            requires
                                0 <= row_counts[i as int] - 1 <= 999,
                                0 <= col_counts[j as int] - 1 <= 999;
                        assert(0 <= (row_counts[i as int] - 1) * (col_counts[j as int] - 1))
                            by (nonlinear_arith)
                            requires
                                0 <= row_counts[i as int] - 1 <= 999,
                                0 <= col_counts[j as int] - 1 <= 999;
                    }
                    let add = (row_counts[i] - 1) * (col_counts[j] - 1);
                    proof {
                        assert(row_counts[i as int] as int == Self::row_ones(grid@, i as int));
                        assert(col_counts[j as int] as int == Self::col_ones(grid@, j as int));
                        assert(add as int == (row_counts[i as int] as int - 1) * (col_counts[j as int] as int - 1));
                        assert(add as int == Self::triangle_at(grid@, i as int, j as int));
                        assert(0 <= add <= 1_000_000);
                        assert(0 <= old_ans <= (i as int * n as int + j as int) * 1_000_000);
                        assert(old_ans + add as int <= (i as int * n as int + j as int) * 1_000_000 + 1_000_000);
                        assert((i as int * n as int + j as int) * 1_000_000 + 1_000_000
                            == (i as int * n as int + j as int + 1) * 1_000_000);
                        assert(old_ans + add as int <= (i as int * n as int + j as int + 1) * 1_000_000);
                        let ii: int = i as int;
                        let jj: int = j as int;
                        let nn: int = n as int;
                        assert(0 <= ii < m as int);
                        assert(0 <= jj < nn);
                        assert(nn <= 1000);
                        assert(m as int <= 1000);
                        assert(ii < 1000);
                        assert(jj < 1000);
                        assert(ii * nn + jj + 1 <= 1_000_000)
                            by (nonlinear_arith)
                            requires
                                0 <= ii,
                                ii < 1000,
                                0 <= jj,
                                jj < 1000,
                                1 <= nn,
                                nn <= 1000;
                        assert((i as int * n as int + j as int + 1) * 1_000_000 <= 1_000_000_000_000);
                        assert(1_000 * 1_000 * 1_000_000 < 9_223_372_036_854_775_807);
                        assert((old_ans + add as int) < 9_223_372_036_854_775_807);
                    }
                    ans = ans + add;
                    proof {
                        assert(ans as int == old_ans + add as int);
                        assert(0 <= ans as int <= (i as int * n as int + j as int + 1) * 1_000_000);
                    }
                } else {
                    proof {
                        assert(0 <= old_ans <= (i as int * n as int + j as int) * 1_000_000);
                        assert((i as int * n as int + j as int) * 1_000_000
                            <= (i as int * n as int + j as int + 1) * 1_000_000);
                        assert(ans as int == old_ans);
                        assert(0 <= ans as int <= (i as int * n as int + j as int + 1) * 1_000_000);
                    }
                }
                proof {
                    if grid[i as int][j as int] == 1 {
                        assert(Self::triangle_at(grid@, i as int, j as int)
                            == (Self::row_ones(grid@, i as int) - 1) * (Self::col_ones(grid@, j as int) - 1));
                    } else {
                        assert(Self::triangle_at(grid@, i as int, j as int) == 0);
                    }
                    assert(Self::row_triangle_sum_prefix(grid@, i as int, j as int + 1)
                        == Self::row_triangle_sum_prefix(grid@, i as int, j as int)
                            + Self::triangle_at(grid@, i as int, j as int));
                    assert(Self::total_triangle_sum_prefix(grid@, i as int)
                        + Self::row_triangle_sum_prefix(grid@, i as int, j as int + 1)
                        == Self::total_triangle_sum_prefix(grid@, i as int)
                            + Self::row_triangle_sum_prefix(grid@, i as int, j as int)
                            + Self::triangle_at(grid@, i as int, j as int));
                }
                j = j + 1;
            }
            proof {
                assert(j == n);
                assert(ans as int == Self::total_triangle_sum_prefix(grid@, i as int)
                    + Self::row_triangle_sum_prefix(grid@, i as int, n as int));
                assert(Self::row_triangle_sum_prefix(grid@, i as int, n as int)
                    == Self::row_triangle_sum_prefix(grid@, i as int, grid[0].len() as int));
                assert(Self::total_triangle_sum_prefix(grid@, i as int + 1)
                    == Self::total_triangle_sum_prefix(grid@, i as int)
                        + Self::row_triangle_sum_prefix(grid@, i as int, grid[0].len() as int));
                assert(0 <= ans as int <= (i as int * n as int + n as int) * 1_000_000);
                let ii: int = i as int;
                let nn: int = n as int;
                assert(ii * nn + nn <= (ii + 1) * nn)
                    by (nonlinear_arith)
                    requires
                        0 <= ii,
                        1 <= nn;
                assert((i as int * n as int + n as int) * 1_000_000 <= (i as int + 1) * n as int * 1_000_000);
            }
            i = i + 1;
        }

        proof {
            assert(i == m);
            assert(ans as int == Self::total_triangle_sum_prefix(grid@, m as int));
            assert(Self::right_triangles_spec(grid@) == Self::total_triangle_sum_prefix(grid@, grid.len() as int));
            assert(grid.len() == m);
        }

        ans
    }
}

}
