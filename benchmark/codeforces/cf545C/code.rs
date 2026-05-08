impl Solution {
    pub fn max_felled_trees(x: Vec<i64>, h: Vec<i64>) -> i64 {
        let n = x.len();
        if n == 1 {
            return 1i64;
        }
        let mut ans: i64 = 2;
        let mut last: i64 = x[0];
        let mut i: usize = 1;
        while i < n - 1 {
            let xi = x[i];
            let hi = h[i];
            if xi > last + hi {
                ans = ans + 1;
                last = xi;
            } else if xi + hi < x[i + 1] {
                ans = ans + 1;
                last = xi + hi;
            } else {
                last = xi;
            }
            i = i + 1;
        }
        ans
    }
}
