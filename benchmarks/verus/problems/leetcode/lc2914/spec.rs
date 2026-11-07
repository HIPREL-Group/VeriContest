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

    pub fn min_changes(s: String) -> (result: i32)
        requires
            2 <= s@.len() <= 100_000,
            s@.len() % 2 == 0,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == '0' || s@[i] == '1',
        ensures
            result == Self::pair_mismatch_prefix(s@, (s@.len() / 2) as int),
    {
    }
}

}
