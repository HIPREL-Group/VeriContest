impl Solution {
    pub fn zigzag_traversal(grid: Vec<Vec<i32>>) -> Vec<i32> {
        let m = grid.len();
        let n = grid[0].len();
        let mut result: Vec<i32> = Vec::new();
        let mut take = true;
        let mut i: usize = 0;
        while i < m {
            let mut s: usize = 0;
            while s < n {
                let col = if i % 2 == 0 { s } else { n - 1 - s };
                let v = grid[i][col];
                if take {
                    result.push(v);
                }
                take = !take;
                s += 1;
            }
            i += 1;
        }
        result
    }
}
