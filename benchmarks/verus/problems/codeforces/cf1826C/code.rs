impl Solution {
    pub fn freedom_possible(n: i64, m: i64) -> bool {
        if n == 1 {
            return true;
        }
        if m >= n {
            return false;
        }
        let mut d: i64 = 2;
        while d * d <= n {
            if n % d == 0 {
                return d > m;
            }
            d = d + 1;
        }
        true
    }
}
