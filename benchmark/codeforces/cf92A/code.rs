impl Solution {
    pub fn presenter_chips(n: u32, m: u32) -> u32 {
        let r_sum: u32 = n * (n + 1) / 2;
        let mut remaining: u32 = m % r_sum;
        let mut walrus: u32 = 1;
        while walrus <= n && remaining >= walrus {
            remaining = remaining - walrus;
            walrus = walrus + 1;
        }
        remaining
    }
}
