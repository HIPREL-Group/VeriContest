impl Solution {
    pub fn find_peak_grid(mat: Vec<Vec<i32>>) -> Vec<i32> {
        let rows = mat.len();
        let cols = mat[0].len();
        let mut best_row: usize = 0;
        let mut best_col: usize = 0;
        let mut best_val = mat[0][0];

        let mut i: usize = 0;
        while i < rows {
            let mut j: usize = 0;
            while j < cols {
                if mat[i][j] > best_val {
                    best_row = i;
                    best_col = j;
                    best_val = mat[i][j];
                }
                j += 1;
            }
            i += 1;
        }

        let mut result = Vec::new();
        result.push(best_row as i32);
        result.push(best_col as i32);
        result
    }
}
