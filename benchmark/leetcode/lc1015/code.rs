impl Solution {
    pub fn smallest_repunit_div_by_k(k: i32) -> i32 {
        let mut r: i32 = 0;
        let mut i: i32 = 0;
        while i < k {
            r = (r * 10 + 1) % k;
            i = i + 1;
            if r == 0 {
                return i;
            }
        }
        -1
    }
}
