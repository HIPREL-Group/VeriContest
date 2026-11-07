impl Solution {
    pub fn min_operations(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut started: bool = false;
        let mut i: usize = 0;
        while i + 1 < n {
            let ai = a[i];
            if ai > 0 {
                ans = ans + ai;
                started = true;
            } else if started {
                ans = ans + 1;
            }
            i = i + 1;
        }
        ans
    }
}
