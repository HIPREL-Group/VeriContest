impl Solution {
    pub fn is_triangular(n: u32) -> bool {
        let mut k: u32 = 1;
        while k <= n {
            if k * (k + 1) / 2 == n {
                return true;
            }
            k = k + 1;
        }
        false
    }
}
