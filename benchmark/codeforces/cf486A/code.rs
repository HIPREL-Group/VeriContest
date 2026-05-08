impl Solution {
    pub fn calculating_function(n: i64) -> i64 {
        if n % 2 == 0 {
            n / 2
        } else {
            -((n + 1) / 2)
        }
    }
}
