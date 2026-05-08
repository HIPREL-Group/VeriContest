use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div(x: int, d: int) -> int {
        (x + d - 1) / d
    }

    pub open spec fn sum_prefix(piles: Seq<i32>, speed: int, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::sum_prefix(piles, speed, n - 1) + Self::ceil_div(piles[n - 1] as int, speed)
        }
    }

    pub open spec fn sum_by_speed(piles: Seq<i32>, speed: int) -> int {
        Self::sum_prefix(piles, speed, piles.len() as int)
    }

    fn sum_with_speed(piles: &Vec<i32>, speed: i32) -> (sum: i64)
        requires
            1 <= piles.len() <= 10_000,
            forall |i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 1_000_000_000,
            1 <= speed <= 1_000_000_000,
        ensures
            sum as int == Self::sum_by_speed(piles@, speed as int),
    {
    }

    pub fn min_eating_speed(piles: Vec<i32>, h: i32) -> (res: i32)
        requires
            1 <= piles.len() <= 10_000,
            forall |i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 1_000_000_000,
            piles.len() <= h <= 1_000_000_000,
        ensures
            1 <= res <= 1_000_000_000,
            Self::sum_by_speed(piles@, res as int) <= h as int,
            forall |k: int| 1 <= k < res ==> #[trigger] Self::sum_by_speed(piles@, k) > h as int,
    {
    }
}

}
