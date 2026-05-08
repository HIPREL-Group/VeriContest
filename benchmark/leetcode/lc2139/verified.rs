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
        while t > 1 && k > 0
            invariant
                1 <= t <= target,
                0 <= k <= max_doubles,
                0 <= moves,
                moves as int + t as int <= target as int + 1,
                moves as int + Self::min_moves_spec(t as int, k as int)
                    == Self::min_moves_spec(target as int, max_doubles as int),
            decreases t,
        {
            if t % 2 == 0 {
                assert(Self::min_moves_spec(t as int, k as int)
                    == 1 + Self::min_moves_spec((t / 2) as int, (k - 1) as int));
                t = t / 2;
                k = k - 1;
            } else {
                assert(Self::min_moves_spec(t as int, k as int)
                    == 1 + Self::min_moves_spec((t - 1) as int, k as int));
                t = t - 1;
            }
            moves = moves + 1;
        }

        assert(t <= 1 || k <= 0);
        if t <= 1 {
            assert(Self::min_moves_spec(t as int, k as int) == 0);
        } else {
            assert(k <= 0);
            assert(Self::min_moves_spec(t as int, k as int) == t as int - 1);
        }
        assert(1 <= t);
        assert(moves as int + t as int - 1 <= target as int) by (nonlinear_arith)
            requires
                moves as int + t as int <= target as int + 1,
                1 <= t,
        ;
        moves + (t - 1)
    }
}

}
