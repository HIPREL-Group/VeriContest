impl Solution {
    pub fn find_diagonal_order(mat: Vec<Vec<i32>>) -> Vec<i32> {
        let rows = mat.len();
        let cols = mat[0].len();
        let total = rows + cols - 1;
        let mut result: Vec<i32> = Vec::new();
        let mut d: usize = 0;
        while d < total {
            let start = if d < cols { 0 } else { d - (cols - 1) };
            let end = if d < rows { d } else { rows - 1 };
            let len = end - start + 1;
            let mut k: usize = 0;
            while k < len {
                let row = if d % 2 == 0 { end - k } else { start + k };
                let col = d - row;
                let v = mat[row][col];
                result.push(v);
                k = k + 1;
            }
            d = d + 1;
        }
        result
    }
}
