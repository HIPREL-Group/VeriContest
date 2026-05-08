impl Solution {
    pub fn can_obtain(n: i64, m: i64) -> bool {
        if n == m {
            true
        } else if n < m || n % 3 != 0 || n < 3 {
            false
        } else {
            let a = n / 3;
            let b = n - a;
            let left = Self::can_obtain(a, m);
            if left {
                true
            } else {
                Self::can_obtain(b, m)
            }
        }
    }
}