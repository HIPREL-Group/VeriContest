use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn modv(x: int) -> int {
        x % 1000000007
    }

    pub open spec fn one_side_ways(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            1
        } else if n == 1 {
            2
        } else {
            Self::modv(Self::one_side_ways(n - 1) + Self::one_side_ways(n - 2))
        }
    }

    pub fn count_house_placements(n: i32) -> (ans: i32)
        requires
            1 <= n <= 10000,
        ensures
            ans as int == Self::modv(Self::one_side_ways(n as int) * Self::one_side_ways(n as int)),
    {
        let m: i64 = 1_000_000_007;
        let mut a: i64 = 1;
        let mut b: i64 = 2;
        let mut i: i32 = 2;
        while i <= n {
            let c = (a + b) % m;
            a = b;
            b = c;
            i = i + 1;
        }
        let one = if n == 1 { 2 } else { b };
        ((one * one) % m) as i32
    }
}

}
