impl Solution {
    pub fn count_orders(n: i32) -> i32 {
        let m: i64 = 1_000_000_007;
        let mut count: i64 = 1;
        let mut i: i64 = 2;
        while i <= n as i64 {
            let factor: i64 = (2 * i - 1) * i;
            count = (count * factor) % m;
            i += 1;
        }
        count as i32
    }
}
