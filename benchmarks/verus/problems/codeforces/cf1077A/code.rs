impl Solution {
    pub fn frog_position_after_jumps(a: i64, b: i64, k: i64) -> i64 {
        let na = (k + 1) / 2;
        let nb = k / 2;
        na * a - nb * b
    }
}
