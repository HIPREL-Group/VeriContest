use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn coin_catchable(y: int) -> bool {
        y >= -1
    }

    pub fn can_catch_coin(x: i32, y: i32) -> (ok: bool)
        requires
            -50 <= x <= 50,
            -50 <= y <= 50,
            !(x == 0 && y == 0),
        ensures
            ok == Self::coin_catchable(y as int),
    {
        let _ = x;
        proof {
            assert((y >= -1) == Self::coin_catchable(y as int));
        }
        y >= -1
    }
}

}
