impl Solution {
    pub fn max_median(n: usize, k: i64, a: Vec<i64>) -> i64 {
        let m = n / 2;
        let mut lo: i64 = a[m];
        let mut hi: i64 = a[m] + k;
        while lo < hi {
            let mid_val: i64 = lo + (hi - lo + 1) / 2;
            let mut cost: i64 = 0;
            let mut i: usize = m;
            while i < n {
                if mid_val > a[i] {
                    cost = cost + (mid_val - a[i]);
                }
                i = i + 1;
            }
            if cost <= k {
                lo = mid_val;
            } else {
                hi = mid_val - 1;
            }
        }
        lo
    }
}
