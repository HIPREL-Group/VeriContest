impl Solution {
    pub fn can_be_the_guy(n: i32, x_levels: Vec<i32>, y_levels: Vec<i32>) -> bool {
        let mut k = 1i32;
        while k <= n {
            let x_len = x_levels.len();
            let y_len = y_levels.len();
            let mut found = false;
            let mut i = 0usize;
            while i < x_len && !found {
                if x_levels[i] == k {
                    found = true;
                } else {
                    i += 1;
                }
            }
            if !found {
                i = 0;
                while i < y_len && !found {
                    if y_levels[i] == k {
                        found = true;
                    } else {
                        i += 1;
                    }
                }
            }
            if !found {
                return false;
            }
            k += 1;
        }
        true
    }
}
