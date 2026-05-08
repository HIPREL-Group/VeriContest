use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn winner_from(n: int, take: int, alice_turn: bool) -> bool
        recommends
            0 <= n,
            0 <= take,
        decreases take
    {
        if take <= 0 || n < take {
            !alice_turn
        } else {
            Self::winner_from(n - take, take - 1, !alice_turn)
        }
    }

    pub fn can_alice_win(n: i32) -> (result: bool)
        requires
            1 <= n <= 50,
        ensures
            result == Self::winner_from(n as int, 10, true),
    {
        let mut stones = n;
        let mut take = 10;
        let mut alice_turn = true;
        while take > 0 && stones >= take
            invariant
                0 <= stones <= n,
                0 <= take <= 10,
                Self::winner_from(stones as int, take as int, alice_turn) == Self::winner_from(n as int, 10, true),
            decreases take
        {
            let ghost prev_stones = stones;
            let ghost prev_take = take;
            let ghost prev_turn = alice_turn;
            proof {
                assert(prev_take > 0);
                assert(prev_stones >= prev_take);
                assert(Self::winner_from(prev_stones as int, prev_take as int, prev_turn)
                    == Self::winner_from((prev_stones - prev_take) as int, (prev_take - 1) as int, !prev_turn));
            }

            stones -= take;
            take -= 1;
            alice_turn = !alice_turn;

            proof {
                assert(stones == prev_stones - prev_take);
                assert(take == prev_take - 1);
                assert(alice_turn == !prev_turn);
                assert(Self::winner_from(stones as int, take as int, alice_turn)
                    == Self::winner_from(prev_stones as int, prev_take as int, prev_turn));
            }
        }

        proof {
            assert(!(take > 0 && stones >= take));
            assert(take <= 0 || stones < take);
            assert(Self::winner_from(stones as int, take as int, alice_turn) == !alice_turn);
            assert(!alice_turn == Self::winner_from(n as int, 10, true));
        }
        !alice_turn
    }
}

}
