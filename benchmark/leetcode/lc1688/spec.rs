use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn matches_spec(n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else if n % 2 == 0 {
            n / 2 + Self::matches_spec(n / 2)
        } else {
            (n - 1) / 2 + Self::matches_spec((n - 1) / 2 + 1)
        }
    }

    pub fn number_of_matches(n: i32) -> (result: i32)
        requires
            1 <= n <= 200,
        ensures
            result == Self::matches_spec(n as int),
    {
    }
}

}
