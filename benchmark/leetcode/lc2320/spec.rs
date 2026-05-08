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
    }
}

}
