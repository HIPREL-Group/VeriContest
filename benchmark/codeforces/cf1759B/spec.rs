use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_seq(s: Seq<u32>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0int } else { s[0] as int + sum_seq(s.subrange(1, s.len() as int)) }
}

pub open spec fn max_seq(s: Seq<u32>) -> u32
    decreases s.len(),
{
    if s.len() == 0 { 0u32 }
    else if s.len() == 1 { s[0] }
    else {
        let rest = max_seq(s.subrange(1, s.len() as int));
        if s[0] > rest { s[0] } else { rest }
    }
}

impl Solution {
    pub fn lost_permutation(b: Vec<u32>, m: usize, s: u32) -> (result: bool)
        requires
            1 <= m <= 50,
            1 <= s <= 1000,
            b.len() == m,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 50,
            forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] != b[j],
        ensures
            result == (
                exists|n: int| max_seq(b@) <= n <= 100 && #[trigger] (n * (n + 1) / 2) == sum_seq(b@) + s as int
            ),
    {
    }
}

}
