impl Solution {
    pub fn final_pos(s: Vec<u8>, t: Vec<u8>) -> usize {
        let mut pos: usize = 0;
        let m = t.len();
        let n = s.len();
        let mut i: usize = 0;
        while i < m {
            if pos < n && s[pos] == t[i] {
                pos = pos + 1;
            }
            i = i + 1;
        }
        pos + 1
    }
}
