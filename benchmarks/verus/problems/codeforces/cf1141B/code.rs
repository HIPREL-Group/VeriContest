impl Solution {
    pub fn maximal_continuous_rest(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut i: usize = 0;
        let total: usize = 2 * n;
        while i < total {
            let idx: usize = i % n;
            if a[idx] == 1 {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}
