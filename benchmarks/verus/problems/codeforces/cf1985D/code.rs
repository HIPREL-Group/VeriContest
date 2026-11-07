impl Solution {
    pub fn manhattan_circle_center(grid: Vec<Vec<i32>>) -> (i32, i32) {
        let n = grid.len();
        let m = grid[0].len();

        let mut found: bool = false;
        let mut min_r: usize = 0usize;
        let mut max_r: usize = 0usize;
        let mut min_c: usize = 0usize;
        let mut max_c: usize = 0usize;

        let mut i: usize = 0usize;
        while i < n {
            let mut j: usize = 0usize;
            while j < m {
                if grid[i][j] == 1 {
                    if !found {
                        found = true;
                        min_r = i;
                        max_r = i;
                        min_c = j;
                        max_c = j;
                    } else {
                        if i < min_r {
                            min_r = i;
                        }
                        if i > max_r {
                            max_r = i;
                        }
                        if j < min_c {
                            min_c = j;
                        }
                        if j > max_c {
                            max_c = j;
                        }
                    }
                }
                j += 1;
            }
            i += 1;
        }

        let center_r = ((min_r + max_r) / 2 + 1) as i32;
        let center_c = ((min_c + max_c) / 2 + 1) as i32;
        (center_r, center_c)
    }
}
