impl Solution {
    pub fn min_penalty(plus_count: i64, minus_count: i64) -> i64 {
        if plus_count >= minus_count {
            plus_count - minus_count
        } else {
            minus_count - plus_count
        }
    }
}
