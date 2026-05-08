impl Solution {
    fn max_additional_exec(k: i128, m: i128) -> i128 {
        let res = m * (2 * k - m - 1) / 2;
        res
    }

    pub fn min_splitters(n: i128, k: i128) -> i128 {
        if n == 1 {
            return 0;
        }
        let need = n - 1;
        let total = Self::max_additional_exec(k, k - 1);
        if need > total {
            return -1;
        }
        let mut lo = 1i128;
        let mut hi = k - 1;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let max_mid = Self::max_additional_exec(k, mid);
            if max_mid >= need {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo
    }
}
