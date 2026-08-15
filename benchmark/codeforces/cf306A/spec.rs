use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occ(s: Seq<u32>, v: u32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() == v { 1int } else { 0int }) + Self::count_occ(s.drop_last(), v)
        }
    }

    pub open spec fn is_perm(a: Seq<u32>, b: Seq<u32>) -> bool {
        a.len() == b.len() && forall|v: u32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub fn distribute(n: u32, m: u32) -> (result: Vec<u32>)
        requires
            1 <= m <= n <= 100,
        ensures
            result.len() == m,
            exists|canonical: Seq<u32>|
                canonical.len() == m as int
                && (forall|i: int| 0 <= i < canonical.len() ==>
                    #[trigger] canonical[i] == (if i < (m as int) - (n as int % m as int) { (n / m) as u32 } else { (n / m + 1) as u32 }))
                && Self::is_perm(result@, canonical),
    {
    }
}

}
