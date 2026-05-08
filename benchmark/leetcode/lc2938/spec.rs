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

    pub fn minimum_steps(s: String) -> (result: i64)
        requires
            1 <= s@.len() <= 100000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == '0' || s@[i] == '1',
        ensures
            result as int == Self::answer_spec(s@),
    {
    }
}

}
