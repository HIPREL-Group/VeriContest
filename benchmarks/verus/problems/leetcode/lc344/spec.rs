use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rev_seq(s: Seq<char>) -> Seq<char> {
        let n: int = s.len() as int;
        Seq::new(s.len(), |i: int| s[n - 1 - i])
    }

    pub fn reverse_string(s: &mut Vec<char>)
        requires
            1 <= old(s).len() <= 100000,
            forall|i: int| 0 <= i < old(s).len() ==> ' ' <= #[trigger] old(s)[i] <= '~',
        ensures
            s@ == Solution::rev_seq((old(s))@),
    {
    }
}

} 
