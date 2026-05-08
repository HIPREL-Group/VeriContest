use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_zeros(s: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        count_zeros(s, k - 1) + (if s[k - 1] == 0u8 { 1int } else { 0int })
    }
}

pub open spec fn count_ones(s: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        count_ones(s, k - 1) + (if s[k - 1] == 1u8 { 1int } else { 0int })
    }
}

impl Solution {
    pub fn minority_count(s: &Vec<u8>) -> (result: u64)
        requires
            1 <= s.len() <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0u8 || s[i] == 1u8,
        ensures
            ({
                let c0 = count_zeros(s@, s.len() as int);
                let c1 = count_ones(s@, s.len() as int);
                if c0 == 0 || c1 == 0 {
                    result as int == 0
                } else if c0 == c1 {
                    result as int == c0 - 1
                } else if c0 < c1 {
                    result as int == c0
                } else {
                    result as int == c1
                }
            }),
    {
    }
}

}
