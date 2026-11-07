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
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < piles.len()
        {
            let pile: i32 = piles[i];
            let p: i64 = pile as i64;
            let s: i64 = speed as i64;
            let term: i64 = (p + s - 1) / s;
            sum += term;
            i += 1;
        }
        sum
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
        let mut max_pile = piles[0];
        let mut i: usize = 1;
        while i < piles.len()
        {
            if piles[i] > max_pile {
                max_pile = piles[i];
            }
            i += 1;
        }

        let mut left: i32 = 1;
        let mut right: i32 = max_pile;

        while left < right
        {
            let mid = left + (right - left) / 2;
            let s = Self::sum_with_speed(&piles, mid);
            if s <= h as i64 {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        left
    }
}

}
