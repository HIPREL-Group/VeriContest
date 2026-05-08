impl Solution {
    pub fn can_square(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut total: i64 = 0;
        let mut k: usize = 0;
        while k < n {
            total = total + a[k];
            k = k + 1;
        }
        let mut lo: i64 = 0;
        let mut hi: i64 = 15_000_000;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid < total {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo * lo == total
    }
}
