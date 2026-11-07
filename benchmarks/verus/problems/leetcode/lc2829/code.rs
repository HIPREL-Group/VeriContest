impl Solution {
    pub fn minimum_sum(n: i32, k: i32) -> i32 {
        let a: i64 = if (n as i64) <= (k as i64) / 2 { n as i64 } else { (k as i64) / 2 };
        let b: i64 = n as i64 - a;
        let left: i64 = a * (a + 1) / 2;
        let right: i64 = b * (2 * k as i64 + b - 1) / 2;
        (left + right) as i32
    }
}
