use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            (if n % 3 == 0 || n % 5 == 0 || n % 7 == 0 { n } else { 0int }) + Self::sum_spec(n - 1)
        }
    }

    pub fn sum_of_multiples(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result == Self::sum_spec(n as int),
    {
    }
}

}
