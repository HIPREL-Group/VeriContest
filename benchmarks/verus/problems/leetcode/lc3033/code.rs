impl Solution {
    pub fn modified_matrix(matrix: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let m = matrix.len();
        let n = matrix[0].len();
        
        let mut col_max: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut mx: i32 = -1;
            let mut i: usize = 0;
            while i < m {
                if matrix[i][j] > mx {
                    mx = matrix[i][j];
                }
                i = i + 1;
            }
            col_max.push(mx);
            j = j + 1;
        }
        
        let mut answer: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                if matrix[i][j] == -1 {
                    row.push(col_max[j]);
                } else {
                    row.push(matrix[i][j]);
                }
                j = j + 1;
            }
            answer.push(row);
            i = i + 1;
        }
        answer
    }
}
