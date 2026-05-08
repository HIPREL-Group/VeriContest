impl Solution {
    pub fn corridor_same_component(
        n: i64,
        m: i64,
        t1: i32,
        y1: i64,
        t2: i32,
        y2: i64,
    ) -> bool {
        let nu = n as u64;
        let mu = m as u64;
        let mut a: u64 = nu;
        let mut b: u64 = mu;
        while b != 0 {
            let rem: u64 = a % b;
            a = b;
            b = rem;
        }
        let g = a;
        let n2 = nu / g;
        let m2 = mu / g;
        let c1 = if t1 == 1 {
            (y1 - 1) / (n2 as i64)
        } else {
            (y1 - 1) / (m2 as i64)
        };
        let c2 = if t2 == 1 {
            (y2 - 1) / (n2 as i64)
        } else {
            (y2 - 1) / (m2 as i64)
        };
        c1 == c2
    }
}
