impl Solution {
    pub fn bun_chocolate_total(n: i64) -> i64 {
        let a = n as u128;
        let m = a * (a + 2);
        let v = m + 2;
        let r = v as i64;
        r
    }
}
