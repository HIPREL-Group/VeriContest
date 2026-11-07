impl Solution {
    pub fn max_toasts(n: u64, k: u64, l: u64, c: u64, d: u64, p: u64, nl: u64, np: u64) -> u64 {
        let drink_toasts = (k * l) / nl;
        let lime_toasts = c * d;
        let salt_toasts = p / np;
        let m1 = if drink_toasts < lime_toasts { drink_toasts } else { lime_toasts };
        let m2 = if m1 < salt_toasts { m1 } else { salt_toasts };
        m2 / n
    }
}
