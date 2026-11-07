use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;





















pub open spec fn has_winning_move(values: Seq<bool>, pos: int, bound: int) -> bool
    decreases bound,
{
    if bound <= 0 {
        false
    } else if bound * bound <= pos && 0 <= pos - bound * bound < values.len()
        && !values[(pos - bound * bound) as int] {
        true
    } else {
        has_winning_move(values, pos, bound - 1)
    }
}




pub open spec fn game_values(n: nat) -> Seq<bool>
    decreases n,
{
    if n == 0 {
        seq![false]
    } else {
        let prev = game_values((n - 1) as nat);
        prev.push(has_winning_move(prev, n as int, n as int))
    }
}



pub open spec fn wins(n: nat) -> bool {
    game_values(n)[n as int]
}

impl Solution {
    pub fn winner_square_game(n: i32) -> (res: bool)
        requires
            1 <= n <= 100000,
        ensures
            res == wins(n as nat),
    {
        let n = n as usize;
        let mut dp: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i <= n {
            dp.push(false);
            i = i + 1;
        }
        i = 1;
        while i <= n {
            let mut k: usize = 1;
            let mut k_sq: usize = 1;
            let mut found: bool = false;
            while k_sq <= i && !found {
                if !dp[i - k_sq] {
                    found = true;
                }
                k = k + 1;
                k_sq = k_sq + 2 * k - 1;
            }
            if found {
                dp.set(i, true);
            }
            i = i + 1;
        }
        dp[n]
    }
}

}
