use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_can_win_nim(n: i32) -> bool {
        n % 4 != 0
    }

    pub fn can_win_nim(n: i32) -> (res: bool)
        requires
            1 <= n as int <= 2_147_483_647,
        ensures
            res == Self::spec_can_win_nim(n),
    {
        n % 4 != 0
    }
}

}
