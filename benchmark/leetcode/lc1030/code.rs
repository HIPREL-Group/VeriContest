impl Solution {
    pub fn all_cells_dist_order(rows: i32, cols: i32, r_center: i32, c_center: i32) -> Vec<Vec<i32>> {
        let max_r_dist = if r_center > rows - 1 - r_center { r_center } else { rows - 1 - r_center };
        let max_c_dist = if c_center > cols - 1 - c_center { c_center } else { cols - 1 - c_center };
        let max_dist = max_r_dist + max_c_dist;
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut d: i32 = 0;
        while d <= max_dist {
            let mut r: i32 = 0;
            while r < rows {
                let mut c: i32 = 0;
                while c < cols {
                    let rd = if r >= r_center { r - r_center } else { r_center - r };
                    let cd = if c >= c_center { c - c_center } else { c_center - c };
                    if rd + cd == d {
                        let mut cell: Vec<i32> = Vec::new();
                        cell.push(r);
                        cell.push(c);
                        result.push(cell);
                    }
                    c = c + 1;
                }
                r = r + 1;
            }
            d = d + 1;
        }
        result
    }
}
