use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn paint_ways(n: int, k: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else if n == 1 {
            k
        } else if n == 2 {
            k * k
        } else {
            (k - 1) * (Self::paint_ways(n - 1, k) + Self::paint_ways(n - 2, k))
        }
    }

    pub fn num_ways(n: i32, k: i32) -> (res: i32)
        requires
            0 <= n <= 50,
            1 <= k <= 100000,
            Self::paint_ways(n as int, k as int) <= i32::MAX as int,
        ensures
            res as int == Self::paint_ways(n as int, k as int),
    {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return k;
        }

        let mut prev2: i32 = k;
        let mut prev1: i32 = k * k;
        let mut i: i32 = 3;
        while i <= n {
            let sum = prev1 + prev2;
            let next = (k - 1) * sum;
            prev2 = prev1;
            prev1 = next;
            i = i + 1;
        }
        prev1
    }
}

}
