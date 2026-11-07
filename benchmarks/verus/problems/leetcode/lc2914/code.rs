impl Solution {
    pub fn min_changes(s: String) -> i32 {
        let len = s.as_str().unicode_len();
        let mut i: usize = 0;
        let mut ans: i32 = 0;

        while i < len {
            let a = s.as_str().get_char(i);
            let b = s.as_str().get_char(i + 1);
            if a != b {
                ans = ans + 1;
            }
            i = i + 2;
        }

        ans
    }
}
