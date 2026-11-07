use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn josephus(n: int, k: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else {
            (Self::josephus(n - 1, k) + k) % n
        }
    }

    pub fn find_the_winner(n: i32, k: i32) -> (result: i32)
        requires
            1 <= k <= n <= 500,
        ensures
            1 <= result <= n,
            result == Self::josephus(n as int, k as int) + 1,
    {
    }
}

}
