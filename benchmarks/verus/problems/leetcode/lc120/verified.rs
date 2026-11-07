use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn path_sum(triangle: Seq<Vec<i32>>, row: int, col: int) -> int
        recommends
            0 <= row < triangle.len(),
            0 <= col < triangle[row].len(),
        decreases triangle.len() - row
    {
        triangle[row][col] as int + if row + 1 >= triangle.len() {
            0
        } else {
            Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1))
        }
    }

    proof fn lemma_path_sum_bounds(triangle: Seq<Vec<i32>>, row: int, col: int)
        requires
            1 <= triangle.len() <= 200,
            triangle[0].len() == 1,
            forall |r: int| 0 <= r < triangle.len() ==> #[trigger] triangle[r].len() == r + 1,
            forall |r: int, c: int|
                0 <= r < triangle.len() && 0 <= c < triangle[r].len() ==> -10000 <= #[trigger] triangle[r][c] <= 10000,
            0 <= row < triangle.len(),
            0 <= col < triangle[row].len(),
        ensures
            -10000 * (triangle.len() - row) <= Self::path_sum(triangle, row, col) <= 10000 * (triangle.len() - row),
        decreases triangle.len() - row
    {
        if row + 1 < triangle.len() {
            Self::lemma_path_sum_bounds(triangle, row + 1, col);
            Self::lemma_path_sum_bounds(triangle, row + 1, col + 1);
            assert(0 <= col + 1 < triangle[row + 1].len()) by {
                assert(triangle[row + 1].len() == row + 2);
                assert(triangle[row].len() == row + 1);
            }
            assert(-10000 * (triangle.len() - (row + 1)) <= Self::path_sum(triangle, row + 1, col));
            assert(Self::path_sum(triangle, row + 1, col) <= 10000 * (triangle.len() - (row + 1)));
            assert(-10000 * (triangle.len() - (row + 1)) <= Self::path_sum(triangle, row + 1, col + 1));
            assert(Self::path_sum(triangle, row + 1, col + 1) <= 10000 * (triangle.len() - (row + 1)));
            assert(-10000 * (triangle.len() - (row + 1))
                <= Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1)));
            assert(Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1))
                <= 10000 * (triangle.len() - (row + 1)));
            assert(-10000 <= triangle[row][col] <= 10000);
            assert(-10000 * (triangle.len() - row) <= Self::path_sum(triangle, row, col)) by (nonlinear_arith)
                requires
                    Self::path_sum(triangle, row, col)
                        == triangle[row][col] as int + Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1)),
                    -10000 <= triangle[row][col] <= 10000,
                    -10000 * (triangle.len() - (row + 1))
                        <= Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1)),
            {}
            assert(Self::path_sum(triangle, row, col) <= 10000 * (triangle.len() - row)) by (nonlinear_arith)
                requires
                    Self::path_sum(triangle, row, col)
                        == triangle[row][col] as int + Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1)),
                    triangle[row][col] <= 10000,
                    Self::min2(Self::path_sum(triangle, row + 1, col), Self::path_sum(triangle, row + 1, col + 1))
                        <= 10000 * (triangle.len() - (row + 1)),
            {}
        }
    }

    fn min_i32(a: i32, b: i32) -> (res: i32)
        ensures
            res as int == Self::min2(a as int, b as int),
    {
        if a <= b { a } else { b }
    }

    pub fn minimum_total(triangle: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= triangle.len() <= 200,
            triangle[0].len() == 1,
            forall |row: int| 0 <= row < triangle.len() ==> #[trigger] triangle[row].len() == row + 1,
            forall |row: int, col: int|
                0 <= row < triangle.len() && 0 <= col < triangle[row].len() ==> -10000 <= #[trigger] triangle[row][col] <= 10000,
        ensures
            res as int == Self::path_sum(triangle@, 0, 0),
    {
        let rows = triangle.len();
        let mut dp = triangle[rows - 1].clone();
        let mut row = rows - 1;
        proof {
            let rows_i = rows as int;
            let row_i = row as int;
            assert(rows_i == triangle.len());
            assert(dp@.len() == triangle@[rows_i - 1].len());
            assert(triangle@[rows_i - 1].len() == rows_i);
            assert forall |col: int| 0 <= col <= row_i implies #[trigger] dp@[col] as int == Self::path_sum(triangle@, row_i, col) by {
                assert(row_i + 1 >= triangle.len());
            };
        }
        while row > 0
            invariant
                rows == triangle.len(),
                1 <= rows <= 200,
                triangle[0].len() == 1,
                forall |r: int| 0 <= r < triangle.len() ==> #[trigger] triangle[r].len() == r + 1,
                forall |r: int, c: int|
                    0 <= r < triangle.len() && 0 <= c < triangle[r].len() ==> -10000 <= #[trigger] triangle[r][c] <= 10000,
                dp@.len() == rows as int,
                0 <= row < rows,
                forall |col: int| 0 <= col <= row as int ==> #[trigger] dp@[col] as int == Self::path_sum(triangle@, row as int, col),
                forall |col: int| 0 <= col <= row as int ==> -10000 * (rows as int - row as int) <= #[trigger] dp@[col] as int <= 10000 * (rows as int - row as int),
            decreases row
        {
            row = row - 1;
            let mut col = 0usize;
            while col <= row
                invariant
                    rows == triangle.len(),
                    1 <= rows <= 200,
                    triangle[0].len() == 1,
                    forall |r: int| 0 <= r < triangle.len() ==> #[trigger] triangle[r].len() == r + 1,
                    forall |r: int, c: int|
                        0 <= r < triangle.len() && 0 <= c < triangle[r].len() ==> -10000 <= #[trigger] triangle[r][c] <= 10000,
                    dp@.len() == rows as int,
                    0 <= row < rows,
                    row + 1 < rows,
                    0 <= col <= row + 1,
                    forall |k: int| 0 <= k < col as int ==> #[trigger] dp@[k] as int == Self::path_sum(triangle@, row as int, k),
                    forall |k: int| col as int <= k <= row as int + 1 ==> #[trigger] dp@[k] as int == Self::path_sum(triangle@, row as int + 1, k),
                    forall |k: int| 0 <= k < col as int ==> -10000 * (rows as int - row as int) <= #[trigger] dp@[k] as int <= 10000 * (rows as int - row as int),
                    forall |k: int| col as int <= k <= row as int + 1 ==> -10000 * (rows as int - (row as int + 1)) <= #[trigger] dp@[k] as int <= 10000 * (rows as int - (row as int + 1)),
                decreases row - col + 1
            {
                proof {
                    let row_i = row as int;
                    let col_i = col as int;
                    assert(row_i + 1 < triangle.len()) by {
                        assert(row + 1 < rows);
                        assert(rows == triangle.len());
                    }
                    assert(col <= row);
                    assert(col < dp.len());
                    assert(col + 1 < dp.len());
                    assert(col_i < triangle@[row_i].len());
                    assert(col_i + 1 < triangle@[row_i + 1].len());
                    Self::lemma_path_sum_bounds(triangle@, row_i + 1, col_i);
                    Self::lemma_path_sum_bounds(triangle@, row_i + 1, col_i + 1);
                }
                let best_child = Self::min_i32(dp[col], dp[col + 1]);
                proof {
                    let row_i = row as int;
                    let col_i = col as int;
                    assert(best_child as int == Self::min2(dp@[col_i] as int, dp@[col_i + 1] as int));
                    assert(best_child as int == Self::min2(Self::path_sum(triangle@, row_i + 1, col_i), Self::path_sum(triangle@, row_i + 1, col_i + 1)));
                    assert(-10000 * (rows as int - (row_i + 1)) <= best_child as int <= 10000 * (rows as int - (row_i + 1)));
                    assert(-10000 <= triangle@[row_i][col_i] <= 10000);
                    assert(0 <= rows as int - (row_i + 1) <= 200) by (nonlinear_arith)
                        requires
                            0 <= row_i,
                            rows <= 200,
                            row_i + 1 < rows as int,
                    {}
                    assert(-2000000 <= -10000 * (rows as int - (row_i + 1))) by (nonlinear_arith)
                        requires
                            0 <= rows as int - (row_i + 1) <= 200,
                    {}
                    assert(10000 * (rows as int - (row_i + 1)) <= 2000000) by (nonlinear_arith)
                        requires
                            0 <= rows as int - (row_i + 1) <= 200,
                    {}
                    assert(-2000000 <= best_child as int) by (nonlinear_arith)
                        requires
                            -2000000 <= -10000 * (rows as int - (row_i + 1)),
                            -10000 * (rows as int - (row_i + 1)) <= best_child as int,
                    {}
                    assert(best_child as int <= 2000000) by (nonlinear_arith)
                        requires
                            best_child as int <= 10000 * (rows as int - (row_i + 1)),
                            10000 * (rows as int - (row_i + 1)) <= 2000000,
                    {}
                    assert(-2010000 <= triangle@[row_i][col_i] as int + best_child as int <= 2010000) by (nonlinear_arith)
                        requires
                            -10000 <= triangle@[row_i][col_i] <= 10000,
                            -2000000 <= best_child as int,
                            best_child as int <= 2000000,
                    {}
                    assert(i32::MIN <= triangle@[row_i][col_i] as int + best_child as int <= i32::MAX) by (nonlinear_arith)
                        requires
                            -2010000 <= triangle@[row_i][col_i] as int + best_child as int <= 2010000,
                    {}
                }
                let value = triangle[row][col] + best_child;
                let ghost old_dp = dp@;
                dp.set(col, value);
                proof {
                    assert(value as int == Self::path_sum(triangle@, row as int, col as int));
                    assert forall |k: int| 0 <= k < col as int + 1 implies #[trigger] dp@[k] as int == Self::path_sum(triangle@, row as int, k) by {
                        if k < col as int {
                            assert(dp@[k] == old_dp[k]);
                        } else {
                            assert(k == col as int);
                        }
                    };
                    assert forall |k: int| col as int + 1 <= k <= row as int + 1 implies #[trigger] dp@[k] as int == Self::path_sum(triangle@, row as int + 1, k) by {
                        assert(dp@[k] == old_dp[k]);
                    };
                    assert forall |k: int| 0 <= k < col as int + 1 implies -10000 * (rows as int - row as int) <= #[trigger] dp@[k] as int <= 10000 * (rows as int - row as int) by {
                        if k < col as int {
                        } else {
                            assert(k == col as int);
                            Self::lemma_path_sum_bounds(triangle@, row as int, k);
                        }
                    };
                    assert forall |k: int| col as int + 1 <= k <= row as int + 1 implies -10000 * (rows as int - (row as int + 1)) <= #[trigger] dp@[k] as int <= 10000 * (rows as int - (row as int + 1)) by {
                        assert(dp@[k] == old_dp[k]);
                    };
                }
                col = col + 1;
            }
        }
        proof {
            assert(row == 0);
            assert(dp@[0] as int == Self::path_sum(triangle@, 0, 0));
        }
        dp[0]
    }
}

}
