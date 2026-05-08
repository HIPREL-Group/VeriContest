impl Solution {
    pub fn check_record(n: i32) -> i32 {
        let m: i64 = 1000000007;
        let mut s00: i64 = 1;
        let mut s01: i64 = 0;
        let mut s02: i64 = 0;
        let mut s10: i64 = 0;
        let mut s11: i64 = 0;
        let mut s12: i64 = 0;

        let mut i: usize = 0;
        while i < n as usize {
            let t00 = (s00 + s01 + s02) % m;
            let t01 = s00;
            let t02 = s01;
            let t10 = (s00 + s01 + s02 + s10 + s11 + s12) % m;
            let t11 = s10;
            let t12 = s11;

            s00 = t00;
            s01 = t01;
            s02 = t02;
            s10 = t10;
            s11 = t11;
            s12 = t12;
            i += 1;
        }

        let ans = (s00 + s01 + s02 + s10 + s11 + s12) % m;
        ans as i32
    }
}
