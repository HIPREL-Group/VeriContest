impl Solution {
    pub fn floor_sqrt_u64(m: u64) -> u64 {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= m {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let r = lo - 1;
        r
    }

    pub fn vasya_pythagorean_triples_count(n: u64) -> u64 {
        let m = 2 * n - 1;
        let k = Self::floor_sqrt_u64(m);
        if k < 3 {
            0
        } else {
            let res = (k + 1) / 2 - 1;
            res
        }
    }
}
