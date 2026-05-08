use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn has_one_prefix(s: Seq<char>, n: int) -> bool
        recommends
            0 <= n <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1',
        decreases n,
    {
        if n <= 0 {
            false
        } else {
            Self::has_one_prefix(s, n - 1) || s[n - 1] == '1'
        }
    }

    pub open spec fn answer_spec(s: Seq<char>, target: Seq<char>) -> bool {
        Self::has_one_prefix(s, s.len() as int) == Self::has_one_prefix(target, target.len() as int)
    }

    pub fn make_strings_equal(s: String, target: String) -> (res: bool)
        requires
            2 <= s@.len() == target@.len() <= 100000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == '0' || s@[i] == '1',
            forall |i: int| 0 <= i < target@.len() ==> target@[i] == '0' || target@[i] == '1',
        ensures
            res == Self::answer_spec(s@, target@),
    {
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

}
