use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn range_sum(sv: Seq<int>, i: int, j: int) -> int
        decreases (if j >= i { j - i + 1 } else { 0 })
    {
        if i > j {
            0
        } else {
            sv[i] + Self::range_sum(sv, i + 1, j)
        }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn max_split_score(sv: Seq<int>, i: int, j: int, k: int) -> int
        recommends 0 <= i, i <= k
        decreases j - i, j - k
    {
        if k >= j || k < i {
            0
        } else {
            let dp_left = if i >= k { 0 } else { Self::max_split_score(sv, i, k, i) };
            let dp_right = if k + 1 >= j { 0 } else { Self::max_split_score(sv, k + 1, j, k + 1) };
            let left = Self::range_sum(sv, i, k);
            let right = Self::range_sum(sv, k + 1, j);
            let score = if left < right {
                left + dp_left
            } else if left > right {
                right + dp_right
            } else {
                Self::spec_max(left + dp_left, right + dp_right)
            };
            Self::spec_max(score, Self::max_split_score(sv, i, j, k + 1))
        }
    }

    pub open spec fn optimal_score(sv: Seq<int>, i: int, j: int) -> int {
        if i >= j { 0 }
        else { Self::max_split_score(sv, i, j, i) }
    }

    pub fn stone_game_v(stone_value: Vec<i32>) -> (result: i32)
        requires
            1 <= stone_value.len() <= 500,
            forall|i: int| 0 <= i < stone_value.len() ==> 1 <= #[trigger] stone_value[i] <= 1_000_000,
        ensures
            result as int == Self::optimal_score(
                stone_value@.map(|_i: int, v: i32| v as int),
                0int,
                stone_value@.len() as int - 1,
            ),
    {
    }
}

}
