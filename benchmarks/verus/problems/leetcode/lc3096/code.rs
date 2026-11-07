impl Solution {
    pub fn minimum_levels(possible: Vec<i32>) -> i32 {
        let n = possible.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            let delta: i64 = if possible[i] == 1 { 1 } else { -1 };
            total = total + delta;
            i += 1;
        }

        let mut prefix: i64 = 0;
        i = 0;

        while i < n - 1 {
            let delta: i64 = if possible[i] == 1 { 1 } else { -1 };
            prefix = prefix + delta;
            if 2 * prefix > total {
                return (i + 1) as i32;
            }
            i += 1;
        }

        -1
    }
}
