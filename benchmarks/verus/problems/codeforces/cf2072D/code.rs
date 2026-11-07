impl Solution {
    pub fn best_shift(a: Vec<i64>) -> (usize, usize) {
        let n = a.len();
        let mut best_l: usize = 0;
        let mut best_r: usize = 0;
        let mut best_delta: i64 = 0;
        let mut l: usize = 0;
        while l < n {
            let mut cur_delta: i64 = 0;
            let mut r: usize = l + 1;
            while r < n {
                if a[r] < a[l] {
                    cur_delta = cur_delta - 1;
                } else if a[r] > a[l] {
                    cur_delta = cur_delta + 1;
                }
                if cur_delta < best_delta {
                    best_delta = cur_delta;
                    best_l = l;
                    best_r = r;
                }
                r = r + 1;
            }
            l = l + 1;
        }
        (best_l, best_r)
    }
}
