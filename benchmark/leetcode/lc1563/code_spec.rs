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
        let n = stone_value.len();
        if n <= 1 {
            return 0;
        }
        let mut pre: Vec<i64> = Vec::new();
        pre.push(0i64);
        let mut idx: usize = 0;
        while idx < n
        {
            pre.push(pre[idx] + stone_value[idx] as i64);
            idx = idx + 1;
        }
        let mut dp: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n * n
        {
            dp.push(0i32);
            idx = idx + 1;
        }
        let mut gap: usize = 1;
        while gap < n
        {
            let mut i: usize = 0;
            while i + gap < n
            {
                let j: usize = i + gap;
                let mut best: i32 = 0;
                let mut k: usize = i;
                while k < j
                {
                    let left_sum: i64 = pre[k + 1] - pre[i];
                    let right_sum: i64 = pre[j + 1] - pre[k + 1];
                    let score: i32;
                    if left_sum < right_sum {
                        score = left_sum as i32 + dp[i * n + k];
                    } else if left_sum > right_sum {
                        score = right_sum as i32 + dp[(k + 1) * n + j];
                    } else {
                        let a: i32 = left_sum as i32 + dp[i * n + k];
                        let b: i32 = right_sum as i32 + dp[(k + 1) * n + j];
                        if a >= b {
                            score = a;
                        } else {
                            score = b;
                        }
                    }
                    if score > best {
                        best = score;
                    }
                    k = k + 1;
                }
                dp.set(i * n + j, best);
                i = i + 1;
            }
            gap = gap + 1;
        }
        dp[n - 1]
    }
}

}
