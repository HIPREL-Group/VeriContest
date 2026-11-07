impl Solution {
    pub fn impossible_face_counts(total: i64, maxima: Vec<i64>) -> Vec<i64> {
        let n = maxima.len();
        let mut sum_all = 0i64;
        let mut i = 0usize;
        while i < n {
            sum_all += maxima[i];
            i += 1;
        }
        let mut res = Vec::new();
        i = 0;
        while i < n {
            let mut lo = total - (sum_all - maxima[i]);
            if lo < 1 {
                lo = 1;
            }
            let mut hi = total - (n as i64 - 1);
            if hi > maxima[i] {
                hi = maxima[i];
            }
            let bad = if hi < lo {
                maxima[i]
            } else if hi == maxima[i] {
                lo - 1
            } else {
                lo - 1 + maxima[i] - hi
            };
            res.push(bad);
            i += 1;
        }
        res
    }
}
