impl Solution {
    pub fn min_days(s: Vec<u8>, f: Vec<u8>) -> usize {
        let mut remove_count: usize = 0;
        let mut add_count: usize = 0;
        let mut i: usize = 0;
        while i < s.len() {
            if s[i] == 1 && f[i] == 0 {
                remove_count = remove_count + 1;
            } else if s[i] == 0 && f[i] == 1 {
                add_count = add_count + 1;
            }
            i = i + 1;
        }
        if remove_count > add_count {
            remove_count
        } else {
            add_count
        }
    }
}
