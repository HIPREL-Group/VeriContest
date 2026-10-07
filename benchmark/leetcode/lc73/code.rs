impl Solution {
    fn set_cell(matrix: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32) {
        let mut current_row = matrix[row].clone();
        current_row[col] = value;
        matrix[row] = current_row;
    }

    fn set_flag(flags: &mut Vec<bool>, idx: usize, value: bool) {
        flags[idx] = value;
    }

    pub fn set_zeroes(matrix: &mut Vec<Vec<i32>>) {
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
