impl Solution {
    pub fn max_teams(n: usize, k: i32, y: Vec<i64>) -> i32 {
        let mut cnt: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if y[i] <= (5 - k) as i64 {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        (cnt / 3) as i32
    }
}
