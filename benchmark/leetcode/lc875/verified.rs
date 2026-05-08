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

    proof fn lemma_ceil_div_mono(x: int, d1: int, d2: int)
        requires
            x >= 1,
            1 <= d1 <= d2,
        ensures
            Solution::ceil_div(x, d1) >= Solution::ceil_div(x, d2),
    {
        assert((x + d1 - 1) / d1 >= (x + d2 - 1) / d2) by (nonlinear_arith)
            requires x >= 1, 1 <= d1 <= d2
        {
        }
    }

    proof fn lemma_sum_mono(piles: Seq<i32>, n: int, s1: int, s2: int)
        requires
            0 <= n <= piles.len(),
            1 <= s1 <= s2,
            forall |i: int| 0 <= i < n ==> 1 <= #[trigger] piles[i],
        ensures
            Solution::sum_prefix(piles, s1, n) >= Solution::sum_prefix(piles, s2, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_sum_mono(piles, n - 1, s1, s2);
            Self::lemma_ceil_div_mono(piles[n - 1] as int, s1, s2);
        }
    }

    proof fn lemma_sum_at_max(piles: Seq<i32>, n: int, k: int)
        requires
            0 <= n <= piles.len(),
            k >= 1,
            forall |i: int| 0 <= i < n ==> 1 <= #[trigger] piles[i] as int <= k,
        ensures
            Solution::sum_prefix(piles, k, n) == n,
        decreases n,
    {
        if n > 0 {
            Self::lemma_sum_at_max(piles, n - 1, k);
            assert(Solution::ceil_div(piles[n - 1] as int, k) == 1) by (nonlinear_arith)
                requires 1 <= piles[n - 1] as int <= k, k >= 1
            {
            }
        }
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
            invariant
                0 <= i <= piles.len(),
                1 <= piles.len() <= 10_000,
                1 <= speed <= 1_000_000_000,
                forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 1_000_000_000,
                sum as int == Self::sum_prefix(piles@, speed as int, i as int),
                0 <= sum as int <= i as int * 1_000_000_000,
            decreases piles.len() - i,
        {
            let pile: i32 = piles[i];
            let p: i64 = pile as i64;
            let s: i64 = speed as i64;
            let term: i64 = (p + s - 1) / s;
            proof {
                assert(pile == piles[i as int]);
                assert(Self::ceil_div(pile as int, speed as int) == (pile as int + speed as int - 1) / speed as int);
                assert(term as int == (pile as int + speed as int - 1) / speed as int);
                assert(term as int == Self::ceil_div(piles[i as int] as int, speed as int));
                assert(1 <= term as int) by (nonlinear_arith)
                    requires 1 <= pile as int, 1 <= speed as int,
                             term as int == (pile as int + speed as int - 1) / speed as int {}
                assert(term as int <= 1_000_000_000) by (nonlinear_arith)
                    requires 1 <= pile as int <= 1_000_000_000, 1 <= speed as int,
                             term as int == (pile as int + speed as int - 1) / speed as int {}
                assert(sum as int + term as int <= (i as int + 1) * 1_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= sum as int <= i as int * 1_000_000_000,
                        1 <= term as int <= 1_000_000_000 {}
                assert((i as int + 1) * 1_000_000_000 <= 10_000 * 1_000_000_000) by (nonlinear_arith)
                    requires i < 10_000 {}
                assert(10_000 * 1_000_000_000 < 9_223_372_036_854_775_807);
            }
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
            invariant
                1 <= piles.len() <= 10_000,
                forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 1_000_000_000,
                1 <= i <= piles.len(),
                1 <= max_pile <= 1_000_000_000,
                forall |j: int| 0 <= j < i as int ==> piles[j] <= max_pile,
            decreases piles.len() - i,
        {
            if piles[i] > max_pile {
                max_pile = piles[i];
            }
            i += 1;
        }

        proof {
            Self::lemma_sum_at_max(piles@, piles.len() as int, max_pile as int);
            assert(Self::sum_by_speed(piles@, max_pile as int) == piles.len() as int);
        }

        let mut left: i32 = 1;
        let mut right: i32 = max_pile;

        while left < right
            invariant
                1 <= left <= right <= max_pile,
                1 <= max_pile <= 1_000_000_000,
                1 <= piles.len() <= 10_000,
                forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 1_000_000_000,
                piles.len() <= h <= 1_000_000_000,
                Self::sum_by_speed(piles@, right as int) <= h as int,
                forall |k: int| 1 <= k < left ==> #[trigger] Self::sum_by_speed(piles@, k) > h as int,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            let s = Self::sum_with_speed(&piles, mid);
            if s <= h as i64 {
                proof {
                    assert(Self::sum_by_speed(piles@, mid as int) == s as int);
                }
                right = mid;
            } else {
                proof {
                    assert(Self::sum_by_speed(piles@, mid as int) > h as int);
                    assert forall |k: int| 1 <= k < mid + 1 implies
                        #[trigger] Self::sum_by_speed(piles@, k) > h as int
                    by {
                        if k < left {
                        } else {
                            Self::lemma_sum_mono(piles@, piles.len() as int, k, mid as int);
                        }
                    }
                }
                left = mid + 1;
            }
        }

        proof {
            assert(left == right);
            assert(Self::sum_by_speed(piles@, left as int) <= h as int);
        }

        left
    }
}

}
