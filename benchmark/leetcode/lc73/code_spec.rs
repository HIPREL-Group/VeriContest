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
        let mut current_row = matrix[row].clone();
        current_row.set(col, value);
        matrix.set(row, current_row);
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
        while row < rows {
            zero_rows.push(false);
            row = row + 1;
        }

        let mut zero_cols: Vec<bool> = Vec::new();
        let mut col = 0usize;
        while col < cols {
            zero_cols.push(false);
            col = col + 1;
        }

        row = 0usize;
        while row < rows {
            let mut has_zero = false;
            col = 0usize;
            while col < cols {
                has_zero = has_zero || matrix[row][col] == 0;
                col = col + 1;
            }
            Self::set_flag(&mut zero_rows, row, has_zero);
            row = row + 1;
        }

        col = 0usize;
        while col < cols {
            let mut has_zero = false;
            row = 0usize;
            while row < rows {
                has_zero = has_zero || matrix[row][col] == 0;
                row = row + 1;
            }
            Self::set_flag(&mut zero_cols, col, has_zero);
            col = col + 1;
        }

        row = 0usize;
        while row < rows {
            col = 0usize;
            while col < cols {
                if zero_rows[row] || zero_cols[col] {
                    Self::set_cell(matrix, row, col, 0);
                }
                col = col + 1;
            }
            row = row + 1;
        }
    }
}

}
