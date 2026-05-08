impl Solution {
    pub fn satisfies_conditions(grid: Vec<Vec<i32>>) -> bool {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut i: usize = 0;
        while i < rows {
            let mut j: usize = 0;
            while j < cols {
                if i + 1 < rows && grid[i][j] != grid[i + 1][j] {
                    return false;
                }
                if j + 1 < cols && grid[i][j] == grid[i][j + 1] {
                    return false;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        true
    }
}
