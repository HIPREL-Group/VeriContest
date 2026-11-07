impl Solution {
    pub fn major_oak_leaves_even(n: i64, k: i64) -> bool {
        let yr_lo = n - k + 1;
        let odds = (n + 1) / 2 - yr_lo / 2;
        odds % 2 == 0
    }
}
