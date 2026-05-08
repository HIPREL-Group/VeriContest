impl Solution {
    pub fn phoenix_balance_min_diff(n: i32) -> i64 {
        let half = n / 2;
        let exp = half + 1;
        let mut p = 1i64;
        let mut k = 0i32;
        while k < exp {
            p = p * 2;
            k = k + 1;
        }
        p - 2
    }
}
