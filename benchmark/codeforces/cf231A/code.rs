impl Solution {
    pub fn count_teams_implement(grid: Vec<i32>, n: usize) -> usize {
        let mut count = 0usize;
        let mut i = 0usize;
        while i < n {
            let idx = 3 * i;
            let s = (grid[idx] as i64) + (grid[idx + 1] as i64) + (grid[idx + 2] as i64);
            if s >= 2 {
                count += 1;
            }
            i += 1;
        }
        count
    }
}
