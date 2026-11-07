impl Solution {
    pub fn is_toeplitz_matrix(matrix: Vec<Vec<i32>>) -> bool
    {
        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut i: usize = 1;
        while i < rows
        {
            let mut j: usize = 1;
            while j < cols
            {
                if matrix[i][j] != matrix[i - 1][j - 1] {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        true
    }
}
