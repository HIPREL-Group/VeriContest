impl Solution {
    pub fn is_anagram(s: String, t: String) -> bool {
        let s_len = s.as_str().unicode_len();
        let t_len = t.as_str().unicode_len();
        if s_len != t_len {
            return false;
        }
        let mut cnt: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < 26 {
            cnt.push(0);
            i += 1;
        }
        i = 0;
        while i < s_len {
            let c = s.as_str().get_char(i);
            let idx = (c as u32 - 97) as usize;
            cnt[idx] = cnt[idx] + 1;
            i += 1;
        }
        i = 0;
        while i < t_len {
            let c = t.as_str().get_char(i);
            let idx = (c as u32 - 97) as usize;
            cnt[idx] = cnt[idx] - 1;
            i += 1;
        }
        let mut k: usize = 0;
        let mut all_zero = true;
        while k < 26 {
            if cnt[k] != 0 {
                all_zero = false;
            }
            k += 1;
        }
        all_zero
    }
}
