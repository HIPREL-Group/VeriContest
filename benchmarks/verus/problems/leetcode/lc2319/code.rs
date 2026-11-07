impl Solution {
    pub fn check_x_matrix(grid: Vec<Vec<i32>>) -> bool {
        let n = grid.len();
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                if i == j || i + j == n - 1 {
                    if grid[i][j] == 0 {
                        return false;
                    }
                } else {
                    if grid[i][j] != 0 {
                        return false;
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        true
    }
}
