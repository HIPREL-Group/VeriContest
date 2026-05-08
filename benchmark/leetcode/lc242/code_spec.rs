use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.last() == c {
        count_char(s.drop_last(), c) + 1
    } else {
        count_char(s.drop_last(), c)
    }
}

pub open spec fn is_lowercase_word(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub open spec fn letter(j: int) -> char {
    (j + 97) as u8 as char
}

pub open spec fn is_anagram_spec(s: Seq<char>, t: Seq<char>) -> bool {
    s.len() == t.len() && forall |j: int| 0 <= j < 26 ==>
        #[trigger] count_char(s, letter(j)) == count_char(t, letter(j))
}

impl Solution {
    pub fn is_anagram(s: String, t: String) -> (res: bool)
        requires
            1 <= s@.len() <= 50_000,
            1 <= t@.len() <= 50_000,
            is_lowercase_word(s@),
            is_lowercase_word(t@),
        ensures
            res == is_anagram_spec(s@, t@),
    {
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
            cnt.set(idx, cnt[idx] + 1);
            i += 1;
        }
        i = 0;
        while i < t_len {
            let c = t.as_str().get_char(i);
            let idx = (c as u32 - 97) as usize;
            cnt.set(idx, cnt[idx] - 1);
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

}
