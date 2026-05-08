impl Solution {
    pub fn n_in_generated_set(n: i64, a: i64, b: i64) -> bool {
        if a == 1 {
            (n - 1) % b == 0
        } else {
            let mut pow: i64 = 1;
            while pow <= n {
                if (n - pow) % b == 0 {
                    return true;
                }
                if pow > n / a {
                    return false;
                }
                pow = pow * a;
            }
            false
        }
    }
}
