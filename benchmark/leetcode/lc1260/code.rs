impl Solution {
    pub fn shift_grid(grid: Vec<Vec<i32>>, k: i32) -> Vec<Vec<i32>> {
        let m: usize = grid.len();
        let n: usize = grid[0].len();
        let total: usize = m * n;
        let k_eff: usize = (k as usize) % total;
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let linear: usize = i * n + j;
                let src: usize = (linear + total - k_eff) % total;
                let src_row: usize = src / n;
                let src_col: usize = src % n;
                row.push(grid[src_row][src_col]);
                j = j + 1;
            }
            result.push(row);
            i = i + 1;
        }
        result
    }
}
