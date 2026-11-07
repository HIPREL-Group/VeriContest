impl Solution {
    pub fn bounding_box(grid: &Vec<Vec<u8>>, n: usize, m: usize) -> (usize, usize, usize, usize) {
        let mut min_r: usize = n;
        let mut max_r: usize = 0;
        let mut min_c: usize = m;
        let mut max_c: usize = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < m {
                if grid[i][j] == 1u8 {
                    if !found {
                        min_r = i;
                        max_r = i;
                        min_c = j;
                        max_c = j;
                        found = true;
                    } else {
                        if i < min_r { min_r = i; }
                        if i > max_r { max_r = i; }
                        if j < min_c { min_c = j; }
                        if j > max_c { max_c = j; }
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        (min_r, max_r, min_c, max_c)
    }
}
