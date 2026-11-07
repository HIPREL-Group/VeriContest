impl Solution {
    pub fn min_balance_seconds(loads: &Vec<i64>) -> i64 {
        let n = loads.len() as i64;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < loads.len() {
            sum = sum + loads[i];
            i = i + 1;
        }
        let base = sum / n;
        let mut rem_high: i64 = sum % n;
        let mut cnt: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= 20000 {
            cnt.push(0);
            j = j + 1;
        }
        let mut k: usize = 0;
        while k < loads.len() {
            let v = loads[k] as usize;
            let oldc = cnt[v];
            cnt[v] = oldc + 1;
            k = k + 1;
        }
        let mut ans: i64 = 0;
        let mut L: i64 = 20000;
        while L >= 0 {
            let c = cnt[L as usize];
            let take = if c < rem_high {
                c
            } else {
                rem_high
            };
            let rest = c - take;
            let d1 = L - base - 1;
            let d2 = L - base;
            let t1 = if d1 > 0 {
                d1
            } else {
                0
            };
            let t2 = if d2 > 0 {
                d2
            } else {
                0
            };
            ans = ans + take * t1 + rest * t2;
            rem_high = rem_high - take;
            L = L - 1;
        }
        ans
    }
}
