impl Solution {
    pub fn pluses_minuses_total_steps(deltas: Vec<i32>) -> i64 {
        let n = deltas.len();
        let mut ans: i64 = n as i64;
        let mut cur: i64 = 0;
        let mut mn: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let i0 = i;
            cur = cur + deltas[i0] as i64;
            if cur < mn {
                ans = ans + (i0 + 1) as i64;
                mn = cur;
            }
            i = i + 1;
        }
        ans
    }
}
