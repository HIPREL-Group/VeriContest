use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn deposit(day: int) -> int {
        (day - 1) / 7 + (day - 1) % 7 + 1
    }

    pub open spec fn total_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { Self::total_spec(n - 1) + Self::deposit(n) }
    }

    pub fn total_money(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result as int == Self::total_spec(n as int),
    {
    }
}

}
