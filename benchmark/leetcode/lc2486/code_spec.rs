use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn matched_prefix(s: Seq<char>, t: Seq<char>, i: int) -> int
        recommends
            0 <= i <= s.len(),
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            let prev = Self::matched_prefix(s, t, i - 1);
            if prev < t.len() && s[i - 1] == t[prev] { prev + 1 } else { prev }
        }
    }

    pub open spec fn answer_spec(s: Seq<char>, t: Seq<char>) -> int {
        t.len() as int - Self::matched_prefix(s, t, s.len() as int)
    }

    pub fn append_characters(s: String, t: String) -> (ans: i32)
        requires
            1 <= s@.len() <= 100000,
            1 <= t@.len() <= 100000,
            forall |i: int| 0 <= i < s@.len() ==> 'a' <= #[trigger] s@[i] <= 'z',
            forall |i: int| 0 <= i < t@.len() ==> 'a' <= #[trigger] t@[i] <= 'z',
        ensures
            0 <= ans as int <= t@.len() as int,
            ans as int == Self::answer_spec(s@, t@),
    {
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

}
