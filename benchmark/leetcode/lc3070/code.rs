impl Solution {
    pub fn count_submatrices(grid: Vec<Vec<i32>>, k: i32) -> i32 {
        let m = grid.len();
        let n = grid[0].len();
        let mut cols: Vec<i64> = Vec::new();
        let mut t: usize = 0;
        while t < n {
            cols.push(0);
            t = t + 1;
        }

        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let k64 = k as i64;
        while i < m {
            let mut row_prefix: i64 = 0;
            let mut j: usize = 0;
            while j < n {
                let old_col = cols[j];
                let new_col = old_col + grid[i][j] as i64;
                cols[j] = new_col;
                row_prefix = row_prefix + new_col;
                if row_prefix <= k64 {
                    ans = ans + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }

        ans as i32
    }
}
