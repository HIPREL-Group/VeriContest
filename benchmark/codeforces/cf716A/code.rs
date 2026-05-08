impl Solution {
    pub fn remaining_words(n: usize, c: i64, t: Vec<i64>) -> usize {
        let mut cnt = 1usize;
        let mut i = 1usize;
        while i < n {
            if t[i] - t[i - 1] <= c {
                cnt = cnt + 1;
            } else {
                cnt = 1;
            }
            i = i + 1;
        }
        cnt
    }
}
