impl Solution {
    pub fn min_chip_teleports(c: Vec<i64>) -> i64 {
        let n = c.len();
        let mut ans: i64 = c[0] - 1;
        let mut j: usize = 0;
        let bound = n - 1;
        while j < bound {
            let ci = c[j];
            let cip1 = c[j + 1];
            let add: i64 = if cip1 > ci {
                cip1 - ci
            } else {
                0
            };
            ans = ans + add;
            j = j + 1;
        }
        ans
    }
}
