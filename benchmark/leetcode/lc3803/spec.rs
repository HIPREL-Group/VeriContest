use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_lowercase_string(s: Seq<char>) -> bool {
        forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
    }

    pub open spec fn is_first_occurrence(s: Seq<char>, idx: nat) -> bool
        recommends
            idx < s.len(),
    {
        forall |q: int| 0 <= q < idx ==> s[q] != s[idx as int]
    }

    pub open spec fn distinct_count_prefix(s: Seq<char>, n: nat) -> int
        recommends
            n <= s.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::distinct_count_prefix(s, (n - 1) as nat)
                + (if Self::is_first_occurrence(s, (n - 1) as nat) { 1int } else { 0int })
        }
    }

    pub open spec fn residue_prefix_count(s: Seq<char>, n: nat) -> int
        recommends
            n <= s.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::residue_prefix_count(s, (n - 1) as nat)
                + (if Self::distinct_count_prefix(s, n) == (n as int) % 3 { 1int } else { 0int })
        }
    }

    pub fn residue_prefixes(s: String) -> (res: i32)
        requires
            1 <= s@.len() <= 100,
            Self::is_lowercase_string(s@),
        ensures
            res as int == Self::residue_prefix_count(s@, s@.len()),
    {
    }
}

}
