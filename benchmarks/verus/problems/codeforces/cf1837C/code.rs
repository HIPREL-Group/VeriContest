impl Solution {
    pub fn best_binary_string(s: Vec<i64>) -> Vec<i64> {
        let n = s.len();
        let mut result: Vec<i64> = Vec::new();
        let mut last: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] != 2 {
                last = s[i];
            }
            result.push(last);
            i = i + 1;
        }
        result
    }
}
