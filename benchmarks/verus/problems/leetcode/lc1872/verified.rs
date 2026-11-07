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

    proof fn prefix_sum_unfold(stones: Seq<i32>, i: int)
        requires
            i >= 0,
        ensures
            Self::prefix_sum(stones, i) == Self::prefix_sum(stones, i - 1) + stones[i] as int,
    {
    }

    proof fn prefix_sum_bounds(stones: Seq<i32>, i: int)
        requires
            0 <= i < stones.len() as int,
            stones.len() <= 100_000,
            forall |k: int| 0 <= k < stones.len() ==> -10_000 <= #[trigger] stones[k] <= 10_000,
        ensures
            -10_000 * (i + 1) <= Self::prefix_sum(stones, i) <= 10_000 * (i + 1),
        decreases i,
    {
        Self::prefix_sum_unfold(stones, i);
        if i > 0 {
            Self::prefix_sum_bounds(stones, i - 1);
        } else {
            assert(Self::prefix_sum(stones, -1 as int) == 0int);
        }
    }

    proof fn optimal_diff_bounds(stones: Seq<i32>, i: int)
        requires
            1 <= i < stones.len() as int,
            2 <= stones.len() <= 100_000,
            forall |k: int| 0 <= k < stones.len() ==> -10_000 <= #[trigger] stones[k] <= 10_000,
        ensures
            -10_000 * stones.len() <= Self::optimal_diff(stones, i) <= 10_000 * stones.len(),
        decreases stones.len() - i,
    {
        if i >= stones.len() - 1 {
            Self::prefix_sum_bounds(stones, stones.len() - 1);
        } else {
            Self::optimal_diff_bounds(stones, i + 1);
            Self::prefix_sum_bounds(stones, i);
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
        let ghost stones_seq = stones@;

        let mut prefix: Vec<i64> = Vec::new();
        let mut sum: i64 = 0;
        let mut i: usize = 0;

        proof {
            assert(sum == Self::prefix_sum(stones_seq, -1 as int));
        }

        while i < n
            invariant
                n == stones.len(),
                stones@ == stones_seq,
                0 <= i <= n,
                2 <= n <= 100_000,
                forall |k: int| 0 <= k < n ==> -10_000 <= #[trigger] stones[k] <= 10_000,
                prefix.len() == i,
                sum == Self::prefix_sum(stones_seq, i as int - 1),
                -10_000 * (i as int) <= sum <= 10_000 * (i as int),
                forall |k: int| 0 <= k < i as int ==> #[trigger] prefix[k] == Self::prefix_sum(stones_seq, k),
                forall |k: int| 0 <= k < i as int ==> -10_000 * (k + 1) <= #[trigger] prefix[k] <= 10_000 * (k + 1),
            decreases n - i,
        {
            proof {
                Self::prefix_sum_unfold(stones_seq, i as int);
                if i > 0 {
                    Self::prefix_sum_bounds(stones_seq, i as int - 1);
                }
            }
            sum = sum + stones[i] as i64;

            proof {
                Self::prefix_sum_bounds(stones_seq, i as int);
            }

            prefix.push(sum);
            i += 1;
        }

        let mut dp: i64 = prefix[n - 1];

        proof {
            assert(dp == Self::prefix_sum(stones_seq, n as int - 1));
        }

        let mut j: usize = n - 2;

        while j >= 1
            invariant
                n == stones.len(),
                stones@ == stones_seq,
                2 <= n <= 100_000,
                forall |k: int| 0 <= k < n ==> -10_000 <= #[trigger] stones[k] <= 10_000,
                prefix.len() == n,
                forall |k: int| 0 <= k < n as int ==> #[trigger] prefix[k] == Self::prefix_sum(stones_seq, k),
                forall |k: int| 0 <= k < n as int ==> -10_000 * (k + 1) <= #[trigger] prefix[k] <= 10_000 * (k + 1),
                0 <= j < n - 1,
                dp == Self::optimal_diff(stones_seq, j as int + 1),
                -10_000 * (n as int) <= dp <= 10_000 * (n as int),
            decreases j,
        {
            proof {
                Self::prefix_sum_bounds(stones_seq, j as int);
            }

            let pick = prefix[j] - dp;
            if pick > dp {
                dp = pick;
            }

            proof {
                Self::optimal_diff_bounds(stones_seq, j as int + 1);
            }

            j -= 1;
        }

        proof {
            assert(j == 0);
            assert(dp == Self::optimal_diff(stones_seq, 1));
            Self::optimal_diff_bounds(stones_seq, 1);
        }

        dp as i32
    }
}

}
