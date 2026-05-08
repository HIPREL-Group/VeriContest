use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pair_mismatch_prefix(s: Seq<char>, pairs: int) -> int
        recommends
            0 <= pairs <= s.len() / 2,
        decreases pairs,
    {
        if pairs <= 0 {
            0
        } else {
            Self::pair_mismatch_prefix(s, pairs - 1)
                + if s[2 * (pairs - 1)] != s[2 * (pairs - 1) + 1] { 1int } else { 0int }
        }
    }

    proof fn lemma_pair_step(s: Seq<char>, p: int)
        requires
            0 <= p < s.len() / 2,
        ensures
            Self::pair_mismatch_prefix(s, p + 1)
                == Self::pair_mismatch_prefix(s, p)
                    + if s[2 * p] != s[2 * p + 1] { 1int } else { 0int },
    {
    }

    pub fn min_changes(s: String) -> (result: i32)
        requires
            2 <= s@.len() <= 100_000,
            s@.len() % 2 == 0,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == '0' || s@[i] == '1',
        ensures
            result == Self::pair_mismatch_prefix(s@, (s@.len() / 2) as int),
    {
        let len = s.as_str().unicode_len();
        let mut i: usize = 0;
        let mut ans: i32 = 0;

        while i < len
            invariant
                len == s@.len(),
                len <= 100_000,
                len % 2 == 0,
                0 <= i <= len,
                i % 2 == 0,
                0 <= ans <= i / 2,
                ans as int == Self::pair_mismatch_prefix(s@, i as int / 2),
            decreases len - i,
        {
            let p = i / 2;
            let a = s.as_str().get_char(i);
            let b = s.as_str().get_char(i + 1);
            if a != b {
                proof {
                    assert(ans <= i / 2);
                    assert(i <= len);
                    assert(len / 2 <= 50_000);
                    assert(ans + 1 <= 50_001);
                    assert(ans + 1 < 2_147_483_647);
                }
                ans = ans + 1;
            }
            proof {
                assert(a == s@[i as int]);
                assert(b == s@[i as int + 1]);
                Self::lemma_pair_step(s@, p as int);
                assert((p as int) == i as int / 2);
                assert(ans as int == Self::pair_mismatch_prefix(s@, p as int + 1));
            }
            i = i + 2;
        }

        ans
    }
}

}
