use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn trailing_zeroes_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            n / 5 + Self::trailing_zeroes_spec(n / 5)
        }
    }

    pub fn trailing_zeroes(n: i32) -> (result: i32)
        requires
            0 <= n <= 10_000,
        ensures
            result as int == Self::trailing_zeroes_spec(n as int),
    {
        let mut remaining = n;
        let mut count = 0;
        while remaining > 0
        {
            remaining = remaining / 5;
            count = count + remaining;
        }
        count
    }
}

}
