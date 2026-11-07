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
        let n = s.len();
        let mut last_one: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 1u8 {
                last_one = i;
            }
            i += 1;
        }
        let mut first_zero: usize = n - 1;
        let mut j: usize = 0;
        let mut found_zero: bool = false;
        while j < n {
            if s[j] == 0u8 && !found_zero {
                first_zero = j;
                found_zero = true;
            }
            j += 1;
        }
        first_zero - last_one + 1
    }
}

}
