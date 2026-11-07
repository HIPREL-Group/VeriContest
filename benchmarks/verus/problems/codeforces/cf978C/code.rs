impl Solution {
    fn locate_dorm(prefix: &Vec<i64>, q: i64) -> i32 {
        let mut lo = 0usize;
        let mut hi = prefix.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if prefix[mid] < q {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo as i32
    }

    pub fn deliver_letters(piles: Vec<i64>, queries: Vec<i64>) -> Vec<(i64, i64)> {
        let mut prefix = Vec::new();
        let mut sum = 0i64;
        let mut i = 0usize;
        while i < piles.len() {
            sum += piles[i];
            prefix.push(sum);
            i += 1;
        }

        let mut res: Vec<(i64, i64)> = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            let idx = Self::locate_dorm(&prefix, queries[qi]) as usize;
            let prev = if idx == 0 { 0i64 } else { prefix[idx - 1] };
            let k = queries[qi] - prev;
            res.push(((idx + 1) as i64, k));
            qi += 1;
        }
        res
    }
}
