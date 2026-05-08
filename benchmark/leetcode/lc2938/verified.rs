use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ones_prefix(s: Seq<char>, n: int) -> int
        recommends
            0 <= n <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1',
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::ones_prefix(s, n - 1) + if s[n - 1] == '1' { 1int } else { 0int }
        }
    }

    pub open spec fn inv_prefix(s: Seq<char>, n: int) -> int
        recommends
            0 <= n <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1',
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::inv_prefix(s, n - 1)
                + if s[n - 1] == '0' { Self::ones_prefix(s, n - 1) } else { 0int }
        }
    }

    pub open spec fn answer_spec(s: Seq<char>) -> int {
        Self::inv_prefix(s, s.len() as int)
    }

    proof fn lemma_ones_step(s: Seq<char>, i: int)
        requires
            0 <= i < s.len(),
            forall |k: int| 0 <= k < s.len() ==> s[k] == '0' || s[k] == '1',
        ensures
            Self::ones_prefix(s, i + 1) == Self::ones_prefix(s, i) + if s[i] == '1' { 1int } else { 0int },
    {
    }

    proof fn lemma_inv_step(s: Seq<char>, i: int)
        requires
            0 <= i < s.len(),
            forall |k: int| 0 <= k < s.len() ==> s[k] == '0' || s[k] == '1',
        ensures
            Self::inv_prefix(s, i + 1)
                == Self::inv_prefix(s, i)
                    + if s[i] == '0' { Self::ones_prefix(s, i) } else { 0int },
    {
    }

    pub fn minimum_steps(s: String) -> (result: i64)
        requires
            1 <= s@.len() <= 100000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == '0' || s@[i] == '1',
        ensures
            result as int == Self::answer_spec(s@),
    {
        let len = s.as_str().unicode_len();
        let mut i: usize = 0;
        let mut ones: i64 = 0;
        let mut steps: i64 = 0;

        while i < len
            invariant
                len == s@.len(),
                1 <= len <= 100000,
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                0 <= i <= len,
                0 <= ones as int == Self::ones_prefix(s@, i as int),
                0 <= steps as int == Self::inv_prefix(s@, i as int),
                ones as int <= i as int,
                ones as int <= 100000,
                steps as int <= (i as int) * 100000,
            decreases len - i,
        {
            let ghost old_i: int = i as int;
            let ghost old_ones: int = ones as int;
            let ghost old_steps: int = steps as int;
            let c = s.as_str().get_char(i);

            proof {
                Self::lemma_ones_step(s@, old_i);
                Self::lemma_inv_step(s@, old_i);
            }

            if c == '1' {
                ones = ones + 1;
            } else {
                proof {
                    assert((steps as int) <= (i as int) * 100000);
                    assert((steps as int) + (ones as int) <= 10000100000);
                    assert((steps as int) + (ones as int) < 9223372036854775807);
                }
                steps = steps + ones;
            }

            proof {
                if c == '1' {
                    assert(ones as int == old_ones + 1);
                    assert(steps as int == old_steps);
                    assert(old_steps <= old_i * 100000);
                    assert((old_i as int) * 100000 <= (old_i + 1) * 100000);
                    assert(steps as int <= (old_i + 1) * 100000);
                } else {
                    assert(ones as int == old_ones);
                    assert(steps as int == old_steps + old_ones);
                    assert(old_steps <= old_i * 100000);
                    assert(old_ones <= 100000);
                    assert(steps as int <= old_i * 100000 + 100000);
                    assert(old_i * 100000 + 100000 == (old_i + 1) * 100000);
                    assert(steps as int <= (old_i + 1) * 100000);
                }
                assert(ones as int == Self::ones_prefix(s@, old_i + 1));
                assert(steps as int == Self::inv_prefix(s@, old_i + 1));
            }

            i = i + 1;
        }

        proof {
            assert(i == len);
            assert(steps as int == Self::inv_prefix(s@, len as int));
            assert(Self::answer_spec(s@) == Self::inv_prefix(s@, s@.len() as int));
            assert(len as int == s@.len() as int);
        }

        steps
    }
}

}
