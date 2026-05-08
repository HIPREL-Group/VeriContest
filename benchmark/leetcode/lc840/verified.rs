use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cols(grid: Seq<Vec<i32>>) -> int {
        if grid.len() > 0 { grid[0].len() as int } else { 0 }
    }

    pub open spec fn candidate_rows(grid: Seq<Vec<i32>>) -> int {
        if grid.len() >= 3 { grid.len() - 2 } else { 0 }
    }

    pub open spec fn candidate_cols(grid: Seq<Vec<i32>>) -> int {
        if Self::cols(grid) >= 3 { Self::cols(grid) - 2 } else { 0 }
    }

    pub open spec fn is_magic_square_at(grid: Seq<Vec<i32>>, r: int, c: int) -> bool
        recommends
            0 <= r < grid.len(),
            0 <= c < Self::cols(grid),
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == Self::cols(grid),
    {
        let a = grid[r][c] as int;
        let b = grid[r][c + 1] as int;
        let c1 = grid[r][c + 2] as int;
        let d = grid[r + 1][c] as int;
        let e = grid[r + 1][c + 1] as int;
        let f = grid[r + 1][c + 2] as int;
        let g = grid[r + 2][c] as int;
        let h = grid[r + 2][c + 1] as int;
        let i = grid[r + 2][c + 2] as int;

        r + 2 < grid.len()
            && c + 2 < Self::cols(grid)
            && 1 <= a <= 9
            && 1 <= b <= 9
            && 1 <= c1 <= 9
            && 1 <= d <= 9
            && 1 <= e <= 9
            && 1 <= f <= 9
            && 1 <= g <= 9
            && 1 <= h <= 9
            && 1 <= i <= 9
            && a != b
            && a != c1
            && a != d
            && a != e
            && a != f
            && a != g
            && a != h
            && a != i
            && b != c1
            && b != d
            && b != e
            && b != f
            && b != g
            && b != h
            && b != i
            && c1 != d
            && c1 != e
            && c1 != f
            && c1 != g
            && c1 != h
            && c1 != i
            && d != e
            && d != f
            && d != g
            && d != h
            && d != i
            && e != f
            && e != g
            && e != h
            && e != i
            && f != g
            && f != h
            && f != i
            && g != h
            && g != i
            && h != i
            && a + b + c1 == 15
            && d + e + f == 15
            && g + h + i == 15
            && a + d + g == 15
            && b + e + h == 15
            && c1 + f + i == 15
            && a + e + i == 15
            && c1 + e + g == 15
    }

    pub open spec fn row_magic_count_prefix(grid: Seq<Vec<i32>>, r: int, j_end: int) -> int
        recommends
            0 <= r < Self::candidate_rows(grid),
            0 <= j_end <= Self::candidate_cols(grid),
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == Self::cols(grid),
        decreases j_end,
    {
        if j_end <= 0 {
            0
        } else {
            Self::row_magic_count_prefix(grid, r, j_end - 1)
                + if Self::is_magic_square_at(grid, r, j_end - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn total_magic_count_prefix(grid: Seq<Vec<i32>>, i_end: int) -> int
        recommends
            0 <= i_end <= Self::candidate_rows(grid),
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == Self::cols(grid),
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            Self::total_magic_count_prefix(grid, i_end - 1)
                + Self::row_magic_count_prefix(grid, i_end - 1, Self::candidate_cols(grid))
        }
    }

    fn is_magic_square(grid: &Vec<Vec<i32>>, r: usize, c: usize) -> (ok: bool)
        requires
            1 <= grid.len() <= 10,
            1 <= grid[0].len() <= 10,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall|i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
            r + 2 < grid.len(),
            c + 2 < grid[0].len(),
        ensures
            ok == Self::is_magic_square_at(grid@, r as int, c as int),
    {
        proof {
            assert(r < grid.len());
            assert(c < grid[0].len());
            assert(c + 1 < grid[0].len());
            assert(c + 2 < grid[0].len());
            assert(r + 1 < grid.len());
            assert(r + 2 < grid.len());
            assert(grid[r as int].len() == grid[0].len());
            assert(grid[(r + 1) as int].len() == grid[0].len());
            assert(grid[(r + 2) as int].len() == grid[0].len());
            assert(c < grid[r as int].len());
            assert(c + 1 < grid[r as int].len());
            assert(c + 2 < grid[r as int].len());
            assert(c < grid[(r + 1) as int].len());
            assert(c + 1 < grid[(r + 1) as int].len());
            assert(c + 2 < grid[(r + 1) as int].len());
            assert(c < grid[(r + 2) as int].len());
            assert(c + 1 < grid[(r + 2) as int].len());
            assert(c + 2 < grid[(r + 2) as int].len());
        }
        let a = grid[r][c];
        let b = grid[r][c + 1];
        let c1 = grid[r][c + 2];
        let d = grid[r + 1][c];
        let e = grid[r + 1][c + 1];
        let f = grid[r + 1][c + 2];
        let g = grid[r + 2][c];
        let h = grid[r + 2][c + 1];
        let i = grid[r + 2][c + 2];

        proof {
            reveal_with_fuel(Solution::is_magic_square_at, 1);
            assert(a as int == grid@[r as int][c as int] as int);
            assert(b as int == grid@[r as int][c as int + 1] as int);
            assert(c1 as int == grid@[r as int][c as int + 2] as int);
            assert(d as int == grid@[(r + 1) as int][c as int] as int);
            assert(e as int == grid@[(r + 1) as int][c as int + 1] as int);
            assert(f as int == grid@[(r + 1) as int][c as int + 2] as int);
            assert(g as int == grid@[(r + 2) as int][c as int] as int);
            assert(h as int == grid@[(r + 2) as int][c as int + 1] as int);
            assert(i as int == grid@[(r + 2) as int][c as int + 2] as int);
        }

        1 <= a
            && a <= 9
            && 1 <= b
            && b <= 9
            && 1 <= c1
            && c1 <= 9
            && 1 <= d
            && d <= 9
            && 1 <= e
            && e <= 9
            && 1 <= f
            && f <= 9
            && 1 <= g
            && g <= 9
            && 1 <= h
            && h <= 9
            && 1 <= i
            && i <= 9
            && a != b
            && a != c1
            && a != d
            && a != e
            && a != f
            && a != g
            && a != h
            && a != i
            && b != c1
            && b != d
            && b != e
            && b != f
            && b != g
            && b != h
            && b != i
            && c1 != d
            && c1 != e
            && c1 != f
            && c1 != g
            && c1 != h
            && c1 != i
            && d != e
            && d != f
            && d != g
            && d != h
            && d != i
            && e != f
            && e != g
            && e != h
            && e != i
            && f != g
            && f != h
            && f != i
            && g != h
            && g != i
            && h != i
            && a + b + c1 == 15
            && d + e + f == 15
            && g + h + i == 15
            && a + d + g == 15
            && b + e + h == 15
            && c1 + f + i == 15
            && a + e + i == 15
            && c1 + e + g == 15
    }

    pub fn num_magic_squares_inside(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 10,
            1 <= grid[0].len() <= 10,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall|i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
        ensures
            result as int == Self::total_magic_count_prefix(grid@, Self::candidate_rows(grid@)),
    {
        let rows = grid.len();
        let cols = grid[0].len();
        let row_limit = if rows >= 3 { rows - 2 } else { 0 };
        let col_limit = if cols >= 3 { cols - 2 } else { 0 };
        let ghost g = grid@;

        proof {
            if rows >= 3 {
                assert(row_limit == rows - 2);
                assert(row_limit as int == g.len() - 2);
            } else {
                assert(row_limit == 0);
            }
            if cols >= 3 {
                assert(col_limit == cols - 2);
                assert(col_limit as int == Self::cols(g) - 2);
            } else {
                assert(col_limit == 0);
            }
            assert(row_limit as int == Self::candidate_rows(g));
            assert(col_limit as int == Self::candidate_cols(g));
        }

        let mut result: i32 = 0;
        let mut r: usize = 0;
        while r < row_limit
            invariant
                g == grid@,
                1 <= grid.len() <= 10,
                1 <= grid[0].len() <= 10,
                rows == grid.len(),
                cols == grid[0].len(),
                row_limit as int == Self::candidate_rows(g),
                col_limit as int == Self::candidate_cols(g),
                forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
                forall|i: int, j: int|
                    0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
                0 <= r <= row_limit,
                result as int == Self::total_magic_count_prefix(g, r as int),
                0 <= result as int <= r as int * col_limit as int,
            decreases row_limit - r,
        {
            let mut c: usize = 0;
            while c < col_limit
                invariant
                    g == grid@,
                    1 <= grid.len() <= 10,
                    1 <= grid[0].len() <= 10,
                    rows == grid.len(),
                    cols == grid[0].len(),
                    row_limit as int == Self::candidate_rows(g),
                    col_limit as int == Self::candidate_cols(g),
                    forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
                    forall|i: int, j: int|
                        0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
                    r < row_limit,
                    0 <= c <= col_limit,
                    result as int
                        == Self::total_magic_count_prefix(g, r as int)
                            + Self::row_magic_count_prefix(g, r as int, c as int),
                    0 <= result as int <= r as int * col_limit as int + c as int,
                decreases col_limit - c,
            {
                let old_result = result;
                let ok = Self::is_magic_square(&grid, r, c);
                if ok {
                        proof {
                            assert(old_result as int <= r as int * col_limit as int + c as int);
                            assert(((r as int) * (col_limit as int)) + (c as int) < 64) by (nonlinear_arith)
                                requires
                                    r < row_limit,
                                    c < col_limit,
                                    row_limit <= 8,
                                    col_limit <= 8;
                            assert(old_result < 2147483647);
                        }
                    result = result + 1;
                }
                proof {
                    reveal_with_fuel(Solution::row_magic_count_prefix, 2);
                    assert(Self::row_magic_count_prefix(g, r as int, c as int + 1)
                        == Self::row_magic_count_prefix(g, r as int, c as int)
                            + if Self::is_magic_square_at(g, r as int, c as int) { 1int } else { 0int });
                    if ok {
                        assert(old_result as int
                            == Self::total_magic_count_prefix(g, r as int)
                                + Self::row_magic_count_prefix(g, r as int, c as int));
                        assert(Self::is_magic_square_at(g, r as int, c as int));
                        assert(result == old_result + 1);
                        assert(result as int
                            == Self::total_magic_count_prefix(g, r as int)
                                + Self::row_magic_count_prefix(g, r as int, c as int + 1));
                    } else {
                        assert(old_result as int
                            == Self::total_magic_count_prefix(g, r as int)
                                + Self::row_magic_count_prefix(g, r as int, c as int));
                        assert(!Self::is_magic_square_at(g, r as int, c as int));
                        assert(result == old_result);
                        assert(result as int
                            == Self::total_magic_count_prefix(g, r as int)
                                + Self::row_magic_count_prefix(g, r as int, c as int + 1));
                    }
                    assert(result as int <= r as int * col_limit as int + (c as int + 1));
                    assert(r as int * col_limit as int + (c as int + 1) <= 64) by (nonlinear_arith)
                        requires
                            r < row_limit,
                            c < col_limit,
                            row_limit <= 8,
                            col_limit <= 8;
                }
                c = c + 1;
            }
            proof {
                reveal_with_fuel(Solution::total_magic_count_prefix, 2);
                assert(Self::total_magic_count_prefix(g, r as int + 1)
                    == Self::total_magic_count_prefix(g, r as int)
                        + Self::row_magic_count_prefix(g, r as int, Self::candidate_cols(g)));
                assert(Self::candidate_cols(g) == col_limit as int);
                assert(result as int == Self::total_magic_count_prefix(g, r as int + 1));
                assert(result as int <= (r as int + 1) * col_limit as int) by (nonlinear_arith)
                    requires result as int <= r as int * col_limit as int + col_limit as int;
            }
            r = r + 1;
        }
        result
    }
}

}
