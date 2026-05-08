impl Solution {
    pub fn flower_game(n: i32, m: i32) -> i64 {
        (((n as u128) * (m as u128)) / 2) as i64
    }
}
