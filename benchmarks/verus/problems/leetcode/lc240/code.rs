impl Solution {
    pub fn search_matrix(matrix: Vec<Vec<i32>>, target: i32) -> bool
    {
        let m = matrix.len() as i32 - 1;
        let n = matrix[0].len() as i32 - 1;

        let mut row = m;
        let mut col = 0;
        while row >= 0 && col <= n 
        {
            let current = matrix[row as usize][col as usize];
            if current == target {
                return true;
            } else if current < target {
                col += 1;
            } else {
                row -= 1;
            }
        }
        false
    }
}
