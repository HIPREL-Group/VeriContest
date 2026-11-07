use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_first_contributing_year(n: int, k: int) -> int {
    n - k + 1
}

pub open spec fn spec_odd_integers_in_interval(L: int, n: int) -> int {
    (n + 1) / 2 - L / 2
}

pub open spec fn spec_major_oak_leaves_even(n: int, k: int) -> bool {
    (spec_odd_integers_in_interval(n - k + 1, n) % 2) == 0
}

impl Solution {
    pub fn major_oak_leaves_even(n: i64, k: i64) -> (r: bool)
        requires
            1 <= n <= 1_000_000_000,
            1 <= k <= n,
        ensures
            r == spec_major_oak_leaves_even(n as int, k as int),
    {
        let yr_lo = n - k + 1;
        proof {
            assert((yr_lo as int) == (n as int) - (k as int) + 1);
            assert(spec_first_contributing_year(n as int, k as int) == (yr_lo as int));
            assert((yr_lo as int) >= 1);
            assert((yr_lo as int) <= (n as int));
        }
        let odds = (n + 1) / 2 - yr_lo / 2;
        proof {
            assert((n + 1) / 2 == ((n as int + 1) / 2) as i64) by {
                assert(0 <= n <= 1_000_000_000);
            };
            assert(yr_lo / 2 == ((yr_lo as int) / 2) as i64) by {
                assert(1 <= yr_lo <= 1_000_000_000);
            };
            assert((odds as int) == (n as int + 1) / 2 - (yr_lo as int) / 2);
            assert((odds as int) == spec_odd_integers_in_interval((yr_lo as int), n as int));
            assert((odds as int) == spec_odd_integers_in_interval(n as int - k as int + 1, n as int));
        }
        proof {
            assert((odds % 2 == 0) == ((odds as int) % 2 == 0));
        }
        odds % 2 == 0
    }
}

}
