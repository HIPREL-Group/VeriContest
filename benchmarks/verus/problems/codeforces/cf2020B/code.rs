impl Solution {
    pub fn floor_sqrt_u64(x: u64) -> u64 {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let r = lo - 1;
        r
    }

    pub fn min_bulbs_n(k: u64) -> u64 {
        let ub = k + 2_000_000_000u64 + 1000u64;
        let mut lo = 1u64;
        let mut hi = ub;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let s = Self::floor_sqrt_u64(mid);
            let cnt = mid - s;
            if cnt >= k {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }
}
