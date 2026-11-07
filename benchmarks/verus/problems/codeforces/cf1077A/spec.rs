use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_jump_delta(a: int, b: int, j: int) -> int {
    if j % 2 == 1 {
        a
    } else {
        -b
    }
}

pub open spec fn spec_frog_after_jumps(a: int, b: int, k: int) -> int
    recommends
        k >= 0,
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        spec_frog_after_jumps(a, b, k - 1) + spec_jump_delta(a, b, k)
    }
}

impl Solution {
    pub fn frog_position_after_jumps(a: i64, b: i64, k: i64) -> (result: i64)
        requires
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            result as int == spec_frog_after_jumps(a as int, b as int, k as int),
            exists|na: int, nb: int|
                na == (k as int + 1) / 2 && nb == (k as int) / 2 && na + nb == k as int && result as int == #[trigger] (na * (a as int) - nb * (b as int)),
    {
    }
}

}
