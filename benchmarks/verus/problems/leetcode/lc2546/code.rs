impl Solution {
    pub fn make_strings_equal(s: String, target: String) -> bool {
        let s_len = s.as_str().unicode_len();
        let t_len = target.as_str().unicode_len();
        let mut i: usize = 0;
        let mut has_s: bool = false;
        while i < s_len {
            if s.as_str().get_char(i) == '1' {
                has_s = true;
            }
            i = i + 1;
        }

        i = 0;
        let mut has_t: bool = false;
        while i < t_len {
            if target.as_str().get_char(i) == '1' {
                has_t = true;
            }
            i = i + 1;
        }

        has_s == has_t
    }
}
