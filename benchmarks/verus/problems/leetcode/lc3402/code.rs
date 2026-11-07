impl Solution {
    pub fn minimum_operations(grid: Vec<Vec<i32>>) -> i32 {
        let m = grid.len();
        let n = grid[0].len();
        let mut ops: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let mut prev: i32 = grid[0][j];
            let mut col_ops: i64 = 0;
            let mut i: usize = 1;
            while i < m {
                let current = grid[i][j];
                let target = if current <= prev { prev + 1 } else { current };
                let inc = target - current;
                col_ops = col_ops + inc as i64;
                prev = target;
                i += 1;
            }
            ops = ops + col_ops;
            j += 1;
        }
        ops as i32
    }
}
