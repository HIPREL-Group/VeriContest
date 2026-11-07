impl Solution {
    pub fn count_negatives(grid: Vec<Vec<i32>>) -> i32 {
        let m = grid.len();
        let n = grid[0].len();
        let mut count = 0;
        let mut i = 0;
        while i < m {
            let mut j = 0;
            while j < n {
                if grid[i][j] < 0 {
                    count += 1;
                }
                j += 1;
            }
            i += 1;
        }
        count
    }
}
