impl Solution {
    pub fn max_score(a: Vec<i64>, s: Vec<u8>) -> i64 {
        let n = a.len();
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        prefix.push(0);
        let mut i: usize = 0;
        while i < n {
            let next = prefix[i] + a[i];
            prefix.push(next);
            i = i + 1;
        }
        let mut total: i64 = 0;
        let mut lo: usize = 0;
        let mut hi: usize = n;
        let mut keep_going: bool = true;
        while keep_going {
            while lo < hi && s[lo] != 1 {
                lo = lo + 1;
            }
            while lo < hi && s[hi - 1] != 2 {
                hi = hi - 1;
            }
            if lo + 1 < hi {
                total = total + prefix[hi] - prefix[lo];
                lo = lo + 1;
                hi = hi - 1;
            } else {
                keep_going = false;
            }
        }
        total
    }
}
