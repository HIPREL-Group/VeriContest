impl Solution {
    pub fn red_last(grid: Vec<u8>) -> bool {
        let mut found: bool = false;
        let mut r: usize = 0;
        while r < 8 {
            let mut all_r: bool = true;
            let mut c: usize = 0;
            while c < 8 {
                if grid[r * 8 + c] != 0 {
                    all_r = false;
                }
                c += 1;
            }
            if all_r {
                found = true;
            }
            r += 1;
        }
        found
    }
}
