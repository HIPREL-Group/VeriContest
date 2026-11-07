use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn first_wins_spec(a: int, b: int, c: int) -> bool {
        if a > b {
            true
        } else if a < b {
            false
        } else {
            (c % 2) == 1
        }
    }

    pub fn first_wins(a: i64, b: i64, c: i64) -> (result: bool)
        requires
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            1 <= c <= 1_000_000_000,
        ensures
            result == Self::first_wins_spec(a as int, b as int, c as int),
    {
        if a > b {
            proof {
                assert((a as int) > (b as int));
                assert(Self::first_wins_spec(a as int, b as int, c as int));
            }
            true
        } else if a < b {
            proof {
                assert((a as int) < (b as int));
                assert(!Self::first_wins_spec(a as int, b as int, c as int));
            }
            false
        } else {
            proof {
                assert((a as int) == (b as int));
                assert(Self::first_wins_spec(a as int, b as int, c as int) == ((c as int % 2) == 1));
                assert(((c % 2) == 1) == ((c as int % 2) == 1));
            }
            (c % 2) == 1
        }
    }
}

}
