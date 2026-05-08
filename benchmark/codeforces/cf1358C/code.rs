impl Solution {
    pub fn celex_distinct_sums(x1: i64, y1: i64, x2: i64, y2: i64) -> i64 {
        let dx = x2 - x1;
        let dy = y2 - y1;
        dx * dy + 1
    }
}
