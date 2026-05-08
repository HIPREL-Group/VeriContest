impl Solution {
    pub fn leftmost_below(n: usize, b: Vec<i64>) -> bool {
        let mut pm: i64 = b[0];
        let mut i: usize = 1;
        while i < n {
            let m: i64 = pm;
            if !(b[i] - m < m) {
                return false;
            }
            if b[i] < pm {
                pm = b[i];
            }
            i = i + 1;
        }
        true
    }
}
