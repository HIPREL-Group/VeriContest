impl Solution {
    pub fn transpose(matrix: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut c: usize = 0;
        while c < cols {
            let mut row: Vec<i32> = Vec::new();
            let mut r: usize = 0;
            while r < rows {
                row.push(matrix[r][c]);
                r += 1;
            }
            result.push(row);
            c += 1;
        }
        result
    }
}
