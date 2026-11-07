impl Solution {
    pub fn one_is_sum_of_others(a: i64, b: i64, c: i64) -> bool {
        a == b + c || b == a + c || c == a + b
    }
}
