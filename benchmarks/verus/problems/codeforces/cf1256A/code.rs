impl Solution {
    pub fn payment_without_change(a: i64, b: i64, n: i64, S: i64) -> bool {
        let x = if a < S / n {
            a
        } else {
            S / n
        };
        let rem = S - x * n;
        rem <= b
    }
}
