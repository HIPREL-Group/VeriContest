impl Solution {
    pub fn surface_area(grid: Vec<Vec<i32>>) -> i32 {
        let n = grid.len();
        let mut res: i32 = 0;
        let mut i: usize = 0;

        while i < n {
            let mut j: usize = 0;
            while j < n {
                if grid[i][j] > 0 {
                    res = res + grid[i][j] * 4 + 2;
                }
                if i > 0 {
                    let a = grid[i][j];
                    let b = grid[i - 1][j];
                    let m = if a <= b { a } else { b };
                    res = res - m * 2;
                }
                if j > 0 {
                    let a = grid[i][j];
                    let b = grid[i][j - 1];
                    let m = if a <= b { a } else { b };
                    res = res - m * 2;
                }
                j += 1;
            }
            i += 1;
        }

        res
    }
}
