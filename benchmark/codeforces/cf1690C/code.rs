impl Solution {
    pub fn restore_durations(s: Vec<i64>, f: Vec<i64>) -> Vec<i64> {
        let n = s.len();
        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            let start = if i == 0 || s[i] > f[i - 1] { s[i] } else { f[i - 1] };
            let dur = f[i] - start;
            result.push(dur);
            i = i + 1;
        }
        result
    }
}
