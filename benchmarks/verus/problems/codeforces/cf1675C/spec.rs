use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;





pub open spec fn rightmost_one(s: Seq<u8>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if s[len - 1] == 1u8 {
        len - 1
    } else {
        rightmost_one(s, len - 1)
    }
}



pub open spec fn leftmost_zero(s: Seq<u8>, start: int) -> int
    decreases s.len() - start,
{
    if start >= s.len() {
        s.len() - 1
    } else if s[start] == 0u8 {
        start
    } else {
        leftmost_zero(s, start + 1)
    }
}

impl Solution {
    pub fn count_suspects(s: Vec<u8>) -> (result: usize)
        requires
            1 <= s.len() <= 200000,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= 2u8,
            rightmost_one(s@, s.len() as int) <= leftmost_zero(s@, 0),
        ensures
            1 <= result <= s.len(),
            result as int == leftmost_zero(s@, 0) - rightmost_one(s@, s.len() as int) + 1,
    {
    }
}

}
