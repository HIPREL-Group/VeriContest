impl Solution {
    pub fn append_characters(s: String, t: String) -> i32 {
        let s_len = s.as_str().unicode_len();
        let t_len = t.as_str().unicode_len();
        let mut i: usize = 0;
        let mut j: usize = 0;

        while i < s_len {
            let c = s.as_str().get_char(i);
            if j < t_len && c == t.as_str().get_char(j) {
                j = j + 1;
            }
            i = i + 1;
        }

        (t_len - j) as i32
    }
}
