impl Solution {
    pub fn minority_count(s: &Vec<u8>) -> u64 {
        let n = s.len();
        let mut c0: u64 = 0;
        let mut c1: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 0u8 {
                c0 = c0 + 1;
            } else {
                c1 = c1 + 1;
            }
            i = i + 1;
        }
        if c0 == 0 || c1 == 0 {
            0
        } else if c0 == c1 {
            c0 - 1
        } else if c0 < c1 {
            c0
        } else {
            c1
        }
    }
}
