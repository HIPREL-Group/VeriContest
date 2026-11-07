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
        let n = stones.len();

        let mut prefix: Vec<i64> = Vec::new();
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + stones[i] as i64;
            prefix.push(sum);
            i += 1;
        }

        let mut dp: i64 = prefix[n - 1];
        let mut j: usize = n - 2;
        while j >= 1 {
            let pick = prefix[j] - dp;
            if pick > dp {
                dp = pick;
            }
            j -= 1;
        }

        dp as i32
    }
}

}
