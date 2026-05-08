impl Solution {
    pub fn projection_area(grid: Vec<Vec<i32>>) -> i32 {
        let n = grid.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;

        while i < n {
            let mut row_max: i32 = 0;
            let mut col_max: i32 = 0;
            let mut top: i32 = 0;
            let mut j: usize = 0;

            while j < n {
                let row_val = grid[i][j];
                let col_val = grid[j][i];

                if row_val > row_max {
                    row_max = row_val;
                }
                if col_val > col_max {
                    col_max = col_val;
                }
                if row_val > 0 {
                    top = top + 1;
                }

                j += 1;
            }

            total = total + row_max + col_max + top;
            i += 1;
        }

        total
    }
}
