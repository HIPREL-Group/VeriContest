impl Solution {
    pub fn construct_game(n: i64, s: i64) -> Option<(Vec<i64>, i64)> {
        if s < 2 * n {
            return None;
        }
        let nu = n as usize;
        let mut a: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < nu - 1 {
            a.push(1i64);
            i = i + 1;
        }
        a.push(s - (n - 1));
        Some((a, n))
    }
}
