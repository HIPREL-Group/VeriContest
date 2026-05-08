impl Solution {
    pub fn top_card(n: usize, a: Vec<i64>, m: usize, b: Vec<i64>) -> i64 {
        let n_i64 = n as i64;
        let mut idx: i64 = 0;
        let mut i: usize = 0;
        while i < m {
            let bi = b[i];
            let s_old: i64 = idx + bi;
            let new_idx: i64 = if s_old >= n_i64 { s_old - n_i64 } else { s_old };
            idx = new_idx;
            i = i + 1;
        }
        a[idx as usize]
    }
}
