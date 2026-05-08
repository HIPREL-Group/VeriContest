impl Solution {
    pub fn reverse_submatrix(grid: Vec<Vec<i32>>, x: i32, y: i32, k: i32) -> Vec<Vec<i32>> {
        let rows = grid.len();
        let cols = grid[0].len();
        let xu = x as usize;
        let yu = y as usize;
        let ku = k as usize;

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < rows {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols {
                let inside = xu <= r && r < xu + ku && yu <= c && c < yu + ku;
                let src_r = if inside { xu + ku - 1 - (r - xu) } else { r };
                let val = grid[src_r][c];
                row.push(val);
                c += 1;
            }
            result.push(row);
            r += 1;
        }

        result
    }
}
