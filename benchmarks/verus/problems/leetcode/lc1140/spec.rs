use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_sum(piles: Seq<i32>, i: int) -> int
        decreases piles.len() - i
    {
        if i >= piles.len() {
            0
        } else {
            piles[i] as int + Self::suffix_sum(piles, i + 1)
        }
    }

    pub open spec fn game(piles: Seq<i32>, i: int, m: int, k: int) -> int
        decreases piles.len() - i, k
        when m >= 1 && k >= 0 && i >= 0
            && (1 <= k && k <= 2 * m ==> i + 2 * m < piles.len())
    {
        if k > 2 * m {
            if i >= piles.len() {
                0
            } else if i + 2 * m >= piles.len() {
                Self::suffix_sum(piles, i)
            } else {
                Self::game(piles, i, m, 2 * m)
            }
        } else if k == 0 {
            0
        } else {
            let new_m = if k > m { k } else { m };
            let score_k = Self::suffix_sum(piles, i)
                - Self::game(piles, i + k, new_m, 2 * new_m + 1);
            if k == 1 {
                score_k
            } else {
                let prev = Self::game(piles, i, m, k - 1);
                if score_k >= prev { score_k } else { prev }
            }
        }
    }

    pub open spec fn optimal(piles: Seq<i32>, i: int, m: int) -> int
    {
        Self::game(piles, i, m, 2 * m + 1)
    }

    pub open spec fn max_score(piles: Seq<i32>, i: int, m: int, k: int) -> int
    {
        Self::game(piles, i, m, k)
    }

    pub fn stone_game_ii(piles: Vec<i32>) -> (result: i32)
        requires
            1 <= piles.len() <= 100,
            forall |i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
        ensures
            result as int == Self::optimal(piles@, 0, 1),
    {
    }
}

}
