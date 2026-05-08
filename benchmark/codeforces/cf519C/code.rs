impl Solution {
    pub fn max_training_teams(n: i64, m: i64) -> i64 {
        let mut ans = if n < m { n } else { m };
        let by_total = (n + m) / 3;
        if by_total < ans {
            ans = by_total;
        }
        ans
    }
}
