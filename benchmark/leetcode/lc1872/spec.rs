use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(stones: Seq<i32>, i: int) -> int
        decreases (if i < 0 { 0 } else { i + 1 }),
    {
        if i < 0 {
            0
        } else {
            Self::prefix_sum(stones, i - 1) + stones[i] as int
        }
    }

    pub open spec fn optimal_diff(stones: Seq<i32>, i: int) -> int
        decreases stones.len() - i,
    {
        if i >= stones.len() - 1 {
            Self::prefix_sum(stones, stones.len() - 1)
        } else {
            let pick = Self::prefix_sum(stones, i) - Self::optimal_diff(stones, i + 1);
            let skip = Self::optimal_diff(stones, i + 1);
            if pick > skip { pick } else { skip }
        }
    }

    pub fn stone_game_viii(stones: Vec<i32>) -> (result: i32)
        requires
            2 <= stones.len() <= 100_000,
            forall |i: int| 0 <= i < stones.len() ==> -10_000 <= #[trigger] stones[i] <= 10_000,
        ensures
            result == Self::optimal_diff(stones@, 1),
    {
    }
}

}
