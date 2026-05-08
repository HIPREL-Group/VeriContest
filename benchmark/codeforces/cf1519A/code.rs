impl Solution {
    pub fn beans_distributable(r: i64, b: i64, d: i64) -> bool {
        let mn = if r <= b { r } else { b };
        let mx = if r <= b { b } else { r };
        if mx == mn {
            true
        } else {
            let q = (mx - 1) / mn;
            q <= d
        }
    }
}
