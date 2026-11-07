use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_count(s: Seq<char>) -> int {
        s.filter(|c: char| c == 'A').len() as int
    }

    pub open spec fn has_three_consec_late(s: Seq<char>) -> bool {
        exists |i: int| 0 <= i <= s.len() - 3 &&
            #[trigger] s[i] == 'L' && s[i+1] == 'L' && s[i+2] == 'L'
    }

    pub open spec fn late_suffix(s: Seq<char>, n: int) -> int
        decreases n, 
    {
        if n <= 0 {
            0
        } else if s[n-1] != 'L' {
            0
        } else {
            1 + Self::late_suffix(s, n-1)
        }
    }

    pub fn check_record(s: String) -> (res: bool)
        requires
            1 <= s@.len() <= 1_000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i] == 'A' || s@[i] == 'L' || s@[i] == 'P',
        ensures
            res <==> (
                Self::abs_count(s@) < 2 &&
                !Self::has_three_consec_late(s@)
            ),
    {
        
    }
}

}