impl Solution {
    pub fn is_symmetric(grid: Vec<u8>) -> bool {
        grid[0] == grid[8] && grid[1] == grid[7] && grid[2] == grid[6] && grid[3] == grid[5]
    }
}
