impl Solution {
    fn gcd_u64(a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            Self::gcd_u64(b, a % b)
        }
    }

    pub fn choose_alarm(x: Vec<i64>, p: Vec<i64>) -> (bool, i64, usize) {
        let n = x.len();
        let mut g: u64 = (x[1] - x[0]) as u64;
        let mut i: usize = 2;
        while i < n {
            let d: u64 = (x[i] - x[i - 1]) as u64;
            g = Self::gcd_u64(g, d);
            i = i + 1;
        }
        let mut jj: usize = 0;
        let m = p.len();
        while jj < m {
            let pv: u64 = p[jj] as u64;
            if g % pv == 0 {
                return (true, x[0], jj);
            }
            jj = jj + 1;
        }
        (false, 0i64, 0usize)
    }
}
