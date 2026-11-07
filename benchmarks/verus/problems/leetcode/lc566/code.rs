impl Solution {
    pub fn matrix_reshape(mat: Vec<Vec<i32>>, r: i32, c: i32) -> Vec<Vec<i32>>
    {
        let m = mat.len();
        let n = mat[0].len();

        if m * n != r as usize * c as usize {
            return mat;
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut ri: usize = 0;
        while ri < r as usize
        {
            let mut row: Vec<i32> = Vec::new();
            let mut ci: usize = 0;
            while ci < c as usize
            {
                row.push(0i32);
                ci += 1;
            }
            result.push(row);
            ri += 1;
        }

        let mut i: usize = 0;
        while i < m
        {
            let mut j: usize = 0;
            while j < n
            {
                let flat: usize = i * n + j;
                let new_row: usize = flat / c as usize;
                let new_col: usize = flat % c as usize;
                let val = mat[i][j];
                let mut row = result[new_row].clone();
                row.set(new_col, val);
                result.set(new_row, row);
                j += 1;
            }
            i += 1;
        }

        result
    }
}
