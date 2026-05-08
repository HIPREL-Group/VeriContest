use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn trailing_zeroes_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            n / 5 + Self::trailing_zeroes_spec(n / 5)
        }
    }

    pub fn trailing_zeroes(n: i32) -> (result: i32)
        requires
            0 <= n <= 10_000,
        ensures
            result as int == Self::trailing_zeroes_spec(n as int),
    {
        let mut remaining = n;
        let mut count = 0;
        while remaining > 0
            invariant
                0 <= remaining <= n,
                0 <= count,
                count as int + Self::trailing_zeroes_spec(remaining as int)
                    == Self::trailing_zeroes_spec(n as int),
                count as int + remaining as int <= n as int,
            decreases remaining,
        {
            let old_remaining = remaining;
            remaining = remaining / 5;
            proof {
                assert(Self::trailing_zeroes_spec(old_remaining as int) == remaining as int
                    + Self::trailing_zeroes_spec(remaining as int));
                assert(remaining <= old_remaining) by (nonlinear_arith)
                    requires
                        old_remaining >= 0,
                        remaining == old_remaining / 5,
                {
                }
                assert(2 * remaining <= old_remaining) by (nonlinear_arith)
                    requires
                        old_remaining >= 0,
                        remaining == old_remaining / 5,
                {
                }
                assert(count as int + remaining as int <= n as int);
                assert(count as int + 2 * remaining as int <= n as int) by (nonlinear_arith)
                    requires
                        count as int + old_remaining as int <= n as int,
                        2 * remaining as int <= old_remaining as int,
                {
                }
            }
            count = count + remaining;
        }
        proof {
            assert(remaining == 0);
            assert(Self::trailing_zeroes_spec(remaining as int) == 0);
        }
        count
    }
}

}
