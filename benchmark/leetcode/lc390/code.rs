impl Solution {
    pub fn last_remaining(n: i32) -> i32 {
        if n <= 1 {
            return n;
        }
        2 * (1 + n / 2 - Self::last_remaining(n / 2))
    }
}
