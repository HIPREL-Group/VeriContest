use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_moves_spec(target: int, max_doubles: int) -> int
        decreases target,
    {
        if target <= 1 {
            0
        } else if max_doubles <= 0 {
            target - 1
        } else if target % 2 == 0 {
            1 + Self::min_moves_spec(target / 2, max_doubles - 1)
        } else {
            1 + Self::min_moves_spec(target - 1, max_doubles)
        }
    }

    pub fn min_moves(target: i32, max_doubles: i32) -> (result: i32)
        requires
            1 <= target <= 1_000_000_000,
            0 <= max_doubles <= 100,
        ensures
            result as int == Self::min_moves_spec(target as int, max_doubles as int),
    {
        let mut t = target;
        let mut k = max_doubles;
        let mut moves = 0;
        while t > 1 && k > 0 {
            if t % 2 == 0 {
                t = t / 2;
                k = k - 1;
            } else {
                t = t - 1;
            }
            moves = moves + 1;
        }
        moves + (t - 1)
    }
}

}
