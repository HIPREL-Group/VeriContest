use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_divisor(n: nat, x: nat) -> bool {
        x >= 1 && x < n && n % x == 0
    }

    pub open spec fn is_winning(n: nat) -> bool
        decreases n
    {
        if n <= 1 {
            false
        } else {
            exists|x: nat| #[trigger] Self::is_divisor(n, x) && !Self::is_winning((n - x) as nat)
        }
    }

    pub fn divisor_game(n: i32) -> (res: bool)
        requires
            1 <= n <= 1000,
        ensures
            res == Self::is_winning(n as nat),
    {
    }
}

}
