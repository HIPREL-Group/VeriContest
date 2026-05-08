use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(stones: Seq<i32>, i: int, j: int) -> int
    decreases (if j >= i { j - i + 1 } else { 0 }),
{
    if i > j {
        0
    } else {
        stones[i] as int + spec_sum(stones, i + 1, j)
    }
}

pub open spec fn spec_optimal_diff(stones: Seq<i32>, i: int, j: int) -> int
    decreases (if j > i { j - i } else { 0 }),
{
    if i >= j {
        0
    } else {
        let left = spec_sum(stones, i + 1, j) - spec_optimal_diff(stones, i + 1, j);
        let right = spec_sum(stones, i, j - 1) - spec_optimal_diff(stones, i, j - 1);
        if left >= right { left } else { right }
    }
}

impl Solution {
    pub fn stone_game_vii(stones: Vec<i32>) -> (res: i32)
        requires
            2 <= stones.len() <= 1000,
            forall |i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 1000,
        ensures
            res as int == spec_optimal_diff(stones@, 0, stones@.len() - 1),
    {
    }
}

}
