impl Solution {
    pub fn reverse_string(s: &mut Vec<char>) {
        let n: usize = s.len();
        let mut i: usize = 0;
        let mut j: usize = n - 1;

        while i < j {
            let tmp = s[i];
            s[i] = s[j];
            s[j] = tmp;
            i += 1;
            j -= 1;
        }
    }
}