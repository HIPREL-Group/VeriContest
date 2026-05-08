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

    proof fn josephus_bounds(n: int, k: int)
        requires
            n >= 1,
            k >= 1,
        ensures
            0 <= Self::josephus(n, k) < n,
        decreases n,
    {
        if n <= 1 {
        } else {
            Self::josephus_bounds(n - 1, k);
        }
    }

    pub fn find_the_winner(n: i32, k: i32) -> (result: i32)
        requires
            1 <= k <= n <= 500,
        ensures
            1 <= result <= n,
            result == Self::josephus(n as int, k as int) + 1,
    {
        let mut winner = 0;
        let mut i = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                1 <= k <= n <= 500,
                winner as int == Self::josephus((i - 1) as int, k as int),
                0 <= winner <= i - 2,
            decreases n - i + 1,
        {
            winner = (winner + k) % i;
            i += 1;
        }
        proof {
            Self::josephus_bounds(n as int, k as int);
        }
        winner + 1
    }
}

}
