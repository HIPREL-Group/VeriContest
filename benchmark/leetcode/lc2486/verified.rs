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

        while i < s_len
            invariant
                s_len == s@.len(),
                t_len == t@.len(),
                1 <= s_len <= 100000,
                1 <= t_len <= 100000,
                forall |k: int| 0 <= k < s@.len() ==> 'a' <= #[trigger] s@[k] <= 'z',
                forall |k: int| 0 <= k < t@.len() ==> 'a' <= #[trigger] t@[k] <= 'z',
                0 <= i <= s_len,
                0 <= j <= t_len,
                j as int == Self::matched_prefix(s@, t@, i as int),
            decreases s_len - i,
        {
            let ghost old_i: int = i as int;
            let ghost old_j: int = j as int;
            let c = s.as_str().get_char(i);
            if j < t_len && c == t.as_str().get_char(j) {
                j = j + 1;
            }
            proof {
                assert(old_j == Self::matched_prefix(s@, t@, old_i));
                assert(Self::matched_prefix(s@, t@, old_i + 1)
                    == if old_j < t@.len() && s@[old_i] == t@[old_j] { old_j + 1 } else { old_j });
                if old_j < t@.len() && s@[old_i] == t@[old_j] {
                    assert(j as int == old_j + 1);
                } else {
                    assert(j as int == old_j);
                }
                assert(j as int == Self::matched_prefix(s@, t@, old_i + 1));
            }
            i = i + 1;
        }

        proof {
            assert(i == s_len);
            assert(j as int == Self::matched_prefix(s@, t@, s_len as int));
            assert(0 <= j as int <= t_len as int);
        }

        (t_len - j) as i32
    }
}

}
