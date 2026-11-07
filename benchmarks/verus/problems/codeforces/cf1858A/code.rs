impl Solution {
    pub fn first_wins(a: i64, b: i64, c: i64) -> bool {
        if a > b {
            true
        } else if a < b {
            false
        } else {
            (c % 2) == 1
        }
    }
}
