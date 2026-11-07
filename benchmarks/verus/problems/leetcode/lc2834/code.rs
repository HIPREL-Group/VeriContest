impl Solution {
    pub fn minimum_possible_sum(n: i32, target: i32) -> i32 {
        let m: i64 = 1_000_000_007;
        let a: i64 = if (n as i64) <= (target as i64) / 2 { n as i64 } else { (target as i64) / 2 };
        let b: i64 = n as i64 - a;
        let left: i64 = a * (a + 1) / 2;
        let right: i64 = b * (2 * target as i64 + b - 1) / 2;
        ((left + right) % m) as i32
    }
}
