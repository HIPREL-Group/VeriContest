impl Solution {
    pub fn island_perimeter(grid: Vec<Vec<i32>>) -> i32 {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut perimeter: i32 = 0;
        let mut r: usize = 0;
        while r < rows {
            let mut c: usize = 0;
            while c < cols {
                if grid[r][c] == 1 {
                    perimeter = perimeter + 4;
                    if r > 0 && grid[r - 1][c] == 1 {
                        perimeter = perimeter - 2;
                    }
                    if c > 0 && grid[r][c - 1] == 1 {
                        perimeter = perimeter - 2;
                    }
                }
                c += 1;
            }
            r += 1;
        }
        perimeter
    }
}
