impl Solution {
    pub fn infinity_table_cell(k: i64) -> (i64, i64) {
        let ku = k as u64;
        let mut lo = 1u64;
        let mut hi = 1_000_000_001u64;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= ku {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let fu = lo - 1;
        let f = fu as i64;
        let s = if f * f == k {
            f
        } else {
            f + 1
        };
        let prev = (s - 1) * (s - 1);
        let off = k - prev;
        if off <= s {
            (off, s)
        } else {
            (s, 2 * s - off)
        }
    }
}
