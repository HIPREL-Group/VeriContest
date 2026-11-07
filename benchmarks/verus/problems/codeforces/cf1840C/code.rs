impl Solution {
    pub fn count_vacations(n: usize, k: usize, q: i64, a: Vec<i64>) -> i64 {
        let mut pos: usize = 0;
        let mut total: i64 = 0;
        while pos < n {
            if a[pos] > q {
                pos += 1;
            } else {
                let start = pos;
                while pos < n && a[pos] <= q {
                    pos += 1;
                }
                let seg_len = pos - start;
                if seg_len >= k {
                    let x = (seg_len - k) as i64 + 1;
                    total += x * (x + 1) / 2;
                }
            }
        }
        total
    }
}
