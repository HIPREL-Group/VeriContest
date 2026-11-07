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

proof fn lemma_spec_sum_snoc(stones: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j,
        j < stones.len(),
    ensures
        spec_sum(stones, i, j) == spec_sum(stones, i, j - 1) + stones[j] as int,
    decreases j - i,
{
    if i == j {
        assert(spec_sum(stones, i + 1, j) == 0);
        assert(spec_sum(stones, i, j - 1) == 0);
    } else {
        lemma_spec_sum_snoc(stones, i + 1, j);
    }
}

proof fn lemma_spec_sum_bounds(stones: Seq<i32>, i: int, j: int)
    requires
        0 <= i,
        j < stones.len(),
        forall |k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 1000,
    ensures
        i > j ==> spec_sum(stones, i, j) == 0,
        i <= j ==> (j - i + 1) <= spec_sum(stones, i, j) <= 1000 * (j - i + 1),
    decreases (if j >= i { j - i + 1 } else { 0 }),
{
    if i <= j {
        lemma_spec_sum_bounds(stones, i + 1, j);
    }
}

proof fn lemma_spec_optimal_diff_bounds(stones: Seq<i32>, i: int, j: int)
    requires
        0 <= i,
        j < stones.len(),
        forall |k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 1000,
    ensures
        0 <= spec_optimal_diff(stones, i, j),
        i <= j ==> spec_optimal_diff(stones, i, j) <= spec_sum(stones, i, j),
        i > j ==> spec_optimal_diff(stones, i, j) == 0,
    decreases (if j > i { j - i } else { 0 }),
{
    if i < j {
        lemma_spec_optimal_diff_bounds(stones, i + 1, j);
        lemma_spec_optimal_diff_bounds(stones, i, j - 1);
        lemma_spec_sum_bounds(stones, i + 1, j);
        lemma_spec_sum_bounds(stones, i, j - 1);
        lemma_spec_sum_bounds(stones, i, j);
        lemma_spec_sum_snoc(stones, i, j);
        assert(spec_sum(stones, i, j) == stones[i] as int + spec_sum(stones, i + 1, j));
        assert(spec_sum(stones, i, j) == spec_sum(stones, i, j - 1) + stones[j] as int);
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
        while k < n
            invariant
                dp.len() == k,
                k <= n,
                forall |idx: int| 0 <= idx < k as int ==> dp@[idx] == 0i32,
            decreases n - k,
        {
            dp.push(0i32);
            k = k + 1;
        }
        let mut i: i32 = n as i32 - 2;
        while i >= 0
            invariant
                -1 <= i <= n as i32 - 2,
                dp@.len() == n as int,
                n == stones@.len(),
                2 <= n <= 1000,
                forall |k: int| 0 <= k < stones@.len() ==> 1 <= #[trigger] stones@[k] <= 1000,
                forall |j: int| (i + 1) as int <= j < n as int ==>
                    dp@[j] as int == spec_optimal_diff(stones@, (i + 1) as int, j),
                forall |j: int| 0 <= j <= i as int ==> dp@[j] == 0i32,
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] dp@[j] <= 1_000_000,
            decreases i + 1,
        {
            let mut total: i32 = stones[i as usize];
            let mut j: usize = (i + 1) as usize;
            proof {
                assert(spec_sum(stones@, (i + 1) as int, i as int) == 0);
                assert(spec_optimal_diff(stones@, i as int, i as int) == 0);
            }
            while j < n
                invariant
                    dp@.len() == n as int,
                    n == stones@.len(),
                    2 <= n <= 1000,
                    0 <= i <= n as i32 - 2,
                    (i + 1) as int <= j as int <= n as int,
                    forall |k: int| 0 <= k < stones@.len() ==> 1 <= #[trigger] stones@[k] <= 1000,
                    total as int == spec_sum(stones@, i as int, (j - 1) as int),
                    1 <= total <= 1_000_000,
                    forall |j2: int| i as int <= j2 < j as int ==>
                        #[trigger] dp@[j2] as int == spec_optimal_diff(stones@, i as int, j2),
                    forall |j2: int| j as int <= j2 < n as int ==>
                        dp@[j2] as int == spec_optimal_diff(stones@, (i + 1) as int, j2),
                    forall |j2: int| 0 <= j2 < i as int ==> dp@[j2] == 0i32,
                    forall |j2: int| 0 <= j2 < n as int ==> 0 <= #[trigger] dp@[j2] <= 1_000_000,
                decreases n - j,
            {
                proof {
                    lemma_spec_sum_snoc(stones@, i as int, j as int);
                    lemma_spec_sum_bounds(stones@, i as int, j as int);
                }
                total = total + stones[j];
                proof {
                    lemma_spec_sum_bounds(stones@, (i + 1) as int, j as int);
                    lemma_spec_sum_bounds(stones@, i as int, (j - 1) as int);
                    lemma_spec_optimal_diff_bounds(stones@, (i + 1) as int, j as int);
                    lemma_spec_optimal_diff_bounds(stones@, i as int, (j - 1) as int);
                }
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
