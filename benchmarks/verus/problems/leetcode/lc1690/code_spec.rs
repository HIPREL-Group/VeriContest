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
        let n = stones.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            dp.push(0i32);
            k = k + 1;
        }
        let mut i: i32 = n as i32 - 2;
        while i >= 0 {
            let mut total: i32 = stones[i as usize];
            let mut j: usize = (i + 1) as usize;
            while j < n {
                total = total + stones[j];
                let left = total - stones[i as usize] - dp[j];
                let right = total - stones[j] - dp[j - 1];
                if left >= right {
                    dp.set(j, left);
                } else {
                    dp.set(j, right);
                }
                j = j + 1;
            }
            i = i - 1;
        }
        dp[n - 1]
    }
}

}
