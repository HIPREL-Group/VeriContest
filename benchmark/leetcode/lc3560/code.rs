impl Solution {
    pub fn min_cutting_cost(n: i32, m: i32, k: i32) -> i64 {
        if n <= k && m <= k {
            0
        } else if n > k {
            let d: i64 = (n as i64) - (k as i64);
            (k as i64) * d
        } else {
            let d: i64 = (m as i64) - (k as i64);
            (k as i64) * d
        }
    }
}
