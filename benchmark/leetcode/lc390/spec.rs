use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn last_remaining_spec(n: int) -> int
        decreases n,
    {
        if n <= 1 {
            n
        } else {
            2 * (1 + n / 2 - Self::last_remaining_spec(n / 2))
        }
    }

    pub fn last_remaining(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result == Self::last_remaining_spec(n as int),
            1 <= result <= n,
    {
    }
}

}
