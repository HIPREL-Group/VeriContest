impl Solution {
    pub fn max_sum(grid: Vec<Vec<i32>>) -> i32 {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut i: usize = 0;
        let mut best_i: usize = 0;
        let mut best_j: usize = 0;
        let mut best = grid[0][0] + grid[0][1] + grid[0][2] + grid[1][1] + grid[2][0] + grid[2][1] + grid[2][2];

        while i + 2 < rows {
            let mut j: usize = 0;
            while j + 2 < cols {
                let sum = grid[i][j]
                    + grid[i][j + 1]
                    + grid[i][j + 2]
                    + grid[i + 1][j + 1]
                    + grid[i + 2][j]
                    + grid[i + 2][j + 1]
                    + grid[i + 2][j + 2];
                if sum > best {
                    let old_best = best;
                    best = sum;
                    best_i = i;
                    best_j = j;
                }
                j += 1;
            }
            i += 1;
        }

        best
    }
}
