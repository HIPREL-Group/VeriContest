use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pow2(k: int) -> int
        decreases k,
    {
        if k <= 0 { 1 } else { 2 * Self::pow2(k - 1) }
    }

    pub open spec fn round_once(s: Seq<i32>) -> Seq<i32> {
        Seq::new(
            s.len() / 2,
            |i: int| {
                if i % 2 == 0 {
                    if s[2 * i] < s[2 * i + 1] { s[2 * i] } else { s[2 * i + 1] }
                } else {
                    if s[2 * i] > s[2 * i + 1] { s[2 * i] } else { s[2 * i + 1] }
                }
            },
        )
    }

    pub open spec fn game_after_steps(s: Seq<i32>, steps: int) -> Seq<i32>
        decreases steps,
    {
        if steps <= 0 || s.len() <= 1 {
            s
        } else {
            Self::game_after_steps(Self::round_once(s), steps - 1)
        }
    }

    pub open spec fn game_result(s: Seq<i32>) -> i32 {
        Self::game_after_steps(s, 10)[0]
    }

    pub fn min_max_game(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1024,
            exists |k: int| 0 <= k <= 10 && nums.len() == Self::pow2(k),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            exists |k: int| 0 <= k <= 10 && nums.len() == Self::pow2(k)
                && Self::game_after_steps(nums@, k) == seq![result],
    {
    }
}

}
