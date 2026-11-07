impl Solution {
    pub fn best_running_miles(b: &Vec<i32>) -> i64 {
        let neg_inf: i64 = -1000000000000000i64;
        let mut res = neg_inf;
        let mut dp1 = neg_inf;
        let mut dp2 = neg_inf;
        let mut i = 0usize;
        while i < b.len() {
            let bi = b[i] as i64;
            let ii = i as i64;
            let cand128: i128 = (dp2 as i128) + (bi as i128) - (ii as i128);
            let res128: i128 = res as i128;
            if cand128 > res128 {
                res = cand128 as i64;
            }
            let t2: i128 = (dp1 as i128) + (bi as i128);
            let dp2_128: i128 = dp2 as i128;
            if t2 > dp2_128 {
                dp2 = t2 as i64;
            }
            let t1: i128 = (bi as i128) + (ii as i128);
            let dp1_128: i128 = dp1 as i128;
            if t1 > dp1_128 {
                dp1 = t1 as i64;
            }
            i = i + 1;
        }
        res
    }
}
