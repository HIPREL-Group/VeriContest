use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_valid_filling(s: Seq<i64>, r: Seq<i64>) -> bool {
        r.len() == s.len()
        && (forall|i: int| 0 <= i < r.len() ==> (#[trigger] r[i] == 0 || r[i] == 1))
        && (forall|i: int| 0 <= i < s.len() && #[trigger] s[i] != 2 ==> r[i] == s[i])
    }

    pub open spec fn descents_from(seq: Seq<i64>, i: int, prev: i64) -> int
        decreases seq.len() - i when i >= 0
    {
        if i >= seq.len() {
            0
        } else {
            (if prev == 1 && seq[i] == 0 { 1int } else { 0int })
                + Self::descents_from(seq, i + 1, seq[i])
        }
    }

    pub open spec fn count_descents(seq: Seq<i64>) -> int {
        if seq.len() == 0 { 0 } else { Self::descents_from(seq, 1, seq[0]) }
    }

    pub fn best_binary_string(s: Vec<i64>) -> (result: Vec<i64>)
        requires
            1 <= s.len() && s.len() <= 300000,
            forall|i: int| 0 <= i < s.len() ==> (#[trigger] s@[i] == 0 || s@[i] == 1 || s@[i] == 2),
        ensures
            result@.len() == s@.len(),
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i] == 0 || result@[i] == 1),
            forall|i: int| 0 <= i < s@.len() && s@[i] != 2 ==> #[trigger] result@[i] == s@[i],
            forall|other: Seq<i64>| #[trigger] Self::is_valid_filling(s@, other)
                ==> Self::count_descents(result@) <= Self::count_descents(other),
    {
    }
}

}
