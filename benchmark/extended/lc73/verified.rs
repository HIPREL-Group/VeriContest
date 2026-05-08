use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_has_zero(matrix: Seq<Vec<i32>>, row: int) -> bool {
        exists |col: int| 0 <= col < matrix[row].len() && matrix[row][col] == 0
    }

    pub open spec fn col_has_zero(matrix: Seq<Vec<i32>>, col: int) -> bool {
        exists |row: int| 0 <= row < matrix.len() && col < matrix[row].len() && matrix[row][col] == 0
    }

    pub open spec fn should_zero(matrix: Seq<Vec<i32>>, row: int, col: int) -> bool {
        Self::row_has_zero(matrix, row) || Self::col_has_zero(matrix, col)
    }

    spec fn row_has_zero_prefix(matrix: Seq<Vec<i32>>, row: int, end_col: int) -> bool {
        exists |col: int| 0 <= col < end_col && matrix[row][col] == 0
    }

    spec fn col_has_zero_prefix(matrix: Seq<Vec<i32>>, col: int, end_row: int) -> bool {
        exists |row: int| 0 <= row < end_row && col < matrix[row].len() && matrix[row][col] == 0
    }

    fn set_cell(matrix: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32)
        requires
            row < old(matrix)@.len(),
            col < old(matrix)@[row as int].len(),
        ensures
            matrix@.len() == old(matrix)@.len(),
            forall |r: int| 0 <= r < matrix@.len() ==> #[trigger] matrix@[r].len() == old(matrix)@[r].len(),
            forall |r: int, c: int|
                0 <= r < matrix@.len() && 0 <= c < matrix@[r].len() ==> #[trigger] matrix@[r][c] == if r == row as int && c == col as int {
                    value
                } else {
                    old(matrix)@[r][c]
                },
    {
        let ghost before = matrix@;
        let mut current_row = matrix[row].clone();
        current_row.set(col, value);
        matrix.set(row, current_row);
        proof {
            assert forall |r: int| 0 <= r < matrix@.len() implies #[trigger] matrix@[r].len() == before[r].len() by {};
            assert forall |r: int, c: int|
                0 <= r < matrix@.len() && 0 <= c < matrix@[r].len()
                implies #[trigger] matrix@[r][c] == if r == row as int && c == col as int {
                    value
                } else {
                    before[r][c]
                }
            by {};
        }
    }

    fn set_flag(flags: &mut Vec<bool>, idx: usize, value: bool)
        requires
            idx < old(flags)@.len(),
        ensures
            flags@.len() == old(flags)@.len(),
            forall |k: int| 0 <= k < flags@.len() ==> #[trigger] flags@[k] == if k == idx as int { value } else { old(flags)@[k] },
    {
        flags.set(idx, value);
    }

    pub fn set_zeroes(matrix: &mut Vec<Vec<i32>>)
        requires
            1 <= (*old(matrix)).len() <= 200,
            1 <= (*old(matrix))[0].len() <= 200,
            forall |row: int| 0 <= row < (*old(matrix)).len() ==> #[trigger] (*old(matrix))[row].len() == (*old(matrix))[0].len(),
            forall |row: int, col: int|
                0 <= row < (*old(matrix)).len() && 0 <= col < (*old(matrix))[row].len() ==> i32::MIN <= #[trigger] (*old(matrix))[row][col] <= i32::MAX,
        ensures
            matrix@.len() == old(matrix)@.len(),
            forall |row: int| 0 <= row < matrix@.len() ==> #[trigger] matrix@[row].len() == old(matrix)@[row].len(),
            forall |row: int, col: int|
                0 <= row < matrix@.len() && 0 <= col < matrix@[row].len() ==> #[trigger] matrix@[row][col] == if Self::should_zero(old(matrix)@, row, col) {
                    0
                } else {
                    old(matrix)@[row][col]
                },
    {
        let rows = matrix.len();
        let cols = matrix[0].len();

        let mut zero_rows: Vec<bool> = Vec::new();
        let mut row = 0usize;
        while row < rows
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                matrix@ =~= old(matrix)@,
                forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                0 <= row <= rows,
                zero_rows@.len() == row as int,
                forall |r: int| 0 <= r < zero_rows@.len() ==> #[trigger] zero_rows@[r] == false,
            decreases rows - row,
        {
            zero_rows.push(false);
            row = row + 1;
        }
        proof {
            assert(zero_rows@.len() == row as int);
            if row < rows {
                assert(false);
            }
            assert(row as int == rows as int) by (nonlinear_arith)
                requires
                    row <= rows,
                    !(row < rows),
            {}
            assert(zero_rows@.len() == rows as int);
        }

        let mut zero_cols: Vec<bool> = Vec::new();
        let mut col = 0usize;
        while col < cols
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                matrix@ =~= old(matrix)@,
                forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                zero_rows@.len() == rows as int,
                forall |r: int| 0 <= r < zero_rows@.len() ==> #[trigger] zero_rows@[r] == false,
                0 <= col <= cols,
                zero_cols@.len() == col as int,
                forall |c: int| 0 <= c < zero_cols@.len() ==> #[trigger] zero_cols@[c] == false,
            decreases cols - col,
        {
            zero_cols.push(false);
            col = col + 1;
        }
        proof {
            assert(zero_cols@.len() == col as int);
            if col < cols {
                assert(false);
            }
            assert(col as int == cols as int) by (nonlinear_arith)
                requires
                    col <= cols,
                    !(col < cols),
            {}
            assert(zero_rows@.len() == rows as int);
            assert(zero_cols@.len() == cols as int);
        }

        row = 0usize;
        while row < rows
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                matrix@ =~= old(matrix)@,
                forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                zero_rows@.len() == rows as int,
                zero_cols@.len() == cols as int,
                forall |c: int| 0 <= c < zero_cols@.len() ==> #[trigger] zero_cols@[c] == false,
                0 <= row <= rows,
                forall |r: int| 0 <= r < row as int ==> #[trigger] zero_rows@[r] == Self::row_has_zero(old(matrix)@, r),
                forall |r: int| row as int <= r < rows as int ==> #[trigger] zero_rows@[r] == false,
            decreases rows - row,
        {
            let mut has_zero = false;
            col = 0usize;
            while col < cols
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    matrix@ =~= old(matrix)@,
                    forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                    zero_rows@.len() == rows as int,
                    zero_cols@.len() == cols as int,
                    forall |c: int| 0 <= c < zero_cols@.len() ==> #[trigger] zero_cols@[c] == false,
                    0 <= row < rows,
                    0 <= col <= cols,
                    has_zero == Self::row_has_zero_prefix(old(matrix)@, row as int, col as int),
                    forall |r: int| 0 <= r < row as int ==> #[trigger] zero_rows@[r] == Self::row_has_zero(old(matrix)@, r),
                    forall |r: int| row as int <= r < rows as int ==> #[trigger] zero_rows@[r] == false,
                decreases cols - col,
            {
                proof {
                    assert(row < matrix.len());
                    assert(col < matrix[row as int].len());
                }
                has_zero = has_zero || matrix[row][col] == 0;
                col = col + 1;
            }
            proof {
                assert(has_zero == Self::row_has_zero_prefix(old(matrix)@, row as int, cols as int));
                assert(has_zero == Self::row_has_zero(old(matrix)@, row as int));
            }
            Self::set_flag(&mut zero_rows, row, has_zero);
            row = row + 1;
        }

        col = 0usize;
        while col < cols
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                matrix@ =~= old(matrix)@,
                forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                zero_rows@.len() == rows as int,
                zero_cols@.len() == cols as int,
                forall |r: int| 0 <= r < rows as int ==> #[trigger] zero_rows@[r] == Self::row_has_zero(old(matrix)@, r),
                0 <= col <= cols,
                forall |c: int| 0 <= c < col as int ==> #[trigger] zero_cols@[c] == Self::col_has_zero(old(matrix)@, c),
                forall |c: int| col as int <= c < cols as int ==> #[trigger] zero_cols@[c] == false,
            decreases cols - col,
        {
            let mut has_zero = false;
            row = 0usize;
            while row < rows
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    matrix@ =~= old(matrix)@,
                    forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                    zero_rows@.len() == rows as int,
                    zero_cols@.len() == cols as int,
                    forall |r: int| 0 <= r < rows as int ==> #[trigger] zero_rows@[r] == Self::row_has_zero(old(matrix)@, r),
                    0 <= col < cols,
                    0 <= row <= rows,
                    has_zero == Self::col_has_zero_prefix(old(matrix)@, col as int, row as int),
                    forall |c: int| 0 <= c < col as int ==> #[trigger] zero_cols@[c] == Self::col_has_zero(old(matrix)@, c),
                    forall |c: int| col as int <= c < cols as int ==> #[trigger] zero_cols@[c] == false,
                decreases rows - row,
            {
                proof {
                    assert(row < matrix.len());
                    assert(col < matrix[row as int].len());
                }
                has_zero = has_zero || matrix[row][col] == 0;
                row = row + 1;
            }
            proof {
                assert(has_zero == Self::col_has_zero_prefix(old(matrix)@, col as int, rows as int));
                assert(has_zero == Self::col_has_zero(old(matrix)@, col as int));
            }
            Self::set_flag(&mut zero_cols, col, has_zero);
            col = col + 1;
        }

        row = 0usize;
        while row < rows
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                zero_rows@.len() == rows as int,
                zero_cols@.len() == cols as int,
                forall |r: int| 0 <= r < rows as int ==> #[trigger] zero_rows@[r] == Self::row_has_zero(old(matrix)@, r),
                forall |c: int| 0 <= c < cols as int ==> #[trigger] zero_cols@[c] == Self::col_has_zero(old(matrix)@, c),
                0 <= row <= rows,
                forall |r: int, c: int|
                    0 <= r < row as int && 0 <= c < cols as int ==> #[trigger] matrix@[r][c] == if Self::should_zero(old(matrix)@, r, c) {
                        0
                    } else {
                        old(matrix)@[r][c]
                    },
                forall |r: int, c: int|
                    row as int <= r < rows as int && 0 <= c < cols as int ==> #[trigger] matrix@[r][c] == old(matrix)@[r][c],
            decreases rows - row,
        {
            col = 0usize;
            while col < cols
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    forall |r: int| 0 <= r < rows as int ==> #[trigger] matrix@[r].len() == cols as int,
                    zero_rows@.len() == rows as int,
                    zero_cols@.len() == cols as int,
                    forall |r: int| 0 <= r < rows as int ==> #[trigger] zero_rows@[r] == Self::row_has_zero(old(matrix)@, r),
                    forall |c: int| 0 <= c < cols as int ==> #[trigger] zero_cols@[c] == Self::col_has_zero(old(matrix)@, c),
                    0 <= row < rows,
                    0 <= col <= cols,
                    forall |r: int, c: int|
                        0 <= r < row as int && 0 <= c < cols as int ==> #[trigger] matrix@[r][c] == if Self::should_zero(old(matrix)@, r, c) {
                            0
                        } else {
                            old(matrix)@[r][c]
                        },
                    forall |c: int|
                        0 <= c < col as int ==> #[trigger] matrix@[row as int][c] == if Self::should_zero(old(matrix)@, row as int, c) {
                            0
                        } else {
                            old(matrix)@[row as int][c]
                        },
                    forall |c: int|
                        col as int <= c < cols as int ==> #[trigger] matrix@[row as int][c] == old(matrix)@[row as int][c],
                    forall |r: int, c: int|
                        (row as int) < r && r < rows as int && 0 <= c && c < cols as int ==> #[trigger] matrix@[r][c] == old(matrix)@[r][c],
                decreases cols - col,
            {
                if zero_rows[row] || zero_cols[col] {
                    Self::set_cell(matrix, row, col, 0);
                }
                col = col + 1;
                proof {
                    assert forall |c: int|
                        0 <= c < col as int
                        implies matrix@[row as int][c] == if Self::should_zero(old(matrix)@, row as int, c) {
                            0
                        } else {
                            old(matrix)@[row as int][c]
                        }
                    by {
                        if c + 1 == col as int {
                            if Self::should_zero(old(matrix)@, row as int, c) {
                                assert(zero_rows@[row as int] || zero_cols@[c]);
                                if zero_rows@[row as int] || zero_cols@[c] {
                                    assert(matrix@[row as int][c] == 0);
                                }
                            } else {
                                assert(!zero_rows@[row as int]);
                                assert(!zero_cols@[c]);
                            }
                        }
                    };
                }
            }
            row = row + 1;
        }
    }
}

}
