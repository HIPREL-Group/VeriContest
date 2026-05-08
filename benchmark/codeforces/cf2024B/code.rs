impl Solution {
    pub fn min_lemonade_presses(n: usize, k: i64, a: Vec<i64>) -> i64 {
        let mut pos = 0usize;
        let mut botnum = 0i64;
        let mut prsnum = 0i64;
        let mut prev_pos = 0usize;
        let mut first = true;
        while pos < n {
            let cnt = (n - pos) as i64;
            let delta = if pos == 0 {
                a[0]
            } else {
                a[pos] - a[pos - 1]
            };
            if !first {
                prsnum = prsnum + ((pos - prev_pos) as i64);
            }
            first = false;
            let prod = cnt * delta;
            if botnum + prod >= k {
                prsnum = prsnum + (k - botnum);
                return prsnum;
            }
            prsnum = prsnum + prod;
            botnum = botnum + prod;
            prev_pos = pos;
            let mut j = pos;
            while j + 1 < n && a[j + 1] == a[j] {
                j = j + 1;
            }
            pos = j + 1;
        }
        prsnum
    }
}
