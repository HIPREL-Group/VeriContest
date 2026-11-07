impl Solution {
    pub fn max_perfect_teams(c: i64, m: i64, x: i64) -> i64 {
        let s = c + m + x;
        let cap = s / 3;
        let mut r = c;
        if m < r {
            r = m;
        }
        if cap < r {
            r = cap;
        }
        r
    }
}
