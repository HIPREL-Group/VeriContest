impl Solution {
    pub fn find_champion(grid: Vec<Vec<i32>>) -> i32 {
        let n = grid.len();

        let mut i: usize = 0;
        while i < n {
            let mut ok = true;
            let mut j: usize = 0;
            while j < n {
                if j != i && grid[i][j] != 1 {
                    ok = false;
                }
                j = j + 1;
            }
            if ok {
                return i as i32;
            }
            i = i + 1;
        }

        0
    }
}
