impl Solution {
    pub fn count_house_placements(n: i32) -> i32 {
        let m: i64 = 1_000_000_007;
        let mut a: i64 = 1;
        let mut b: i64 = 2;
        let mut i: i32 = 2;
        while i <= n {
            let c = (a + b) % m;
            a = b;
            b = c;
            i = i + 1;
        }
        let one = if n == 1 { 2 } else { b };
        ((one * one) % m) as i32
    }
}
