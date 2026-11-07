use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_prefix(weights: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::sum_prefix(weights, n - 1) + weights[n - 1] as int
        }
    }

    pub open spec fn sum_weights(weights: Seq<i32>) -> int {
        Self::sum_prefix(weights, weights.len() as int)
    }

    pub open spec fn max_prefix(weights: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 1 {
            weights[0] as int
        } else {
            let prev = Self::max_prefix(weights, n - 1);
            let cur = weights[n - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn max_weight(weights: Seq<i32>) -> int {
        Self::max_prefix(weights, weights.len() as int)
    }

    pub open spec fn days_needed_rec(weights: Seq<i32>, cap: int, i: int, cur: int, used: int) -> int
        decreases weights.len() as int - i
    {
        if i >= weights.len() {
            used
        } else {
            let w = weights[i] as int;
            if cur + w <= cap {
                Self::days_needed_rec(weights, cap, i + 1, cur + w, used)
            } else {
                Self::days_needed_rec(weights, cap, i + 1, w, used + 1)
            }
        }
    }

    pub open spec fn days_needed(weights: Seq<i32>, cap: int) -> int {
        Self::days_needed_rec(weights, cap, 0, 0, 1)
    }

    pub fn ship_within_days(weights: Vec<i32>, days: i32) -> (res: i32)
        requires
            1 <= days <= weights.len() <= 50_000,
            forall |i: int| 0 <= i < weights.len() ==> 1 <= #[trigger] weights[i] <= 500,
        ensures
            Self::max_weight(weights@) <= res as int <= Self::sum_weights(weights@),
            Self::days_needed(weights@, res as int) <= days as int,
            res as int == Self::max_weight(weights@)
                || Self::days_needed(weights@, res as int - 1) > days as int,
    {
        let mut max_w = weights[0];
        let mut sum_w = weights[0];
        let mut i = 1usize;
        while i < weights.len()
        {
            if weights[i] > max_w {
                max_w = weights[i];
            }
            sum_w += weights[i];
            i += 1;
        }

        let mut low = max_w;
        let mut high = sum_w;

        while low < high
        {
            let mid = low + (high - low) / 2;
            let mut need = 1;
            let mut cur = 0;
            let mut j = 0usize;
            while j < weights.len()
            {
                if cur + weights[j] > mid {
                    need += 1;
                    cur = weights[j];
                } else {
                    cur += weights[j];
                }
                j += 1;
            }

            if need <= days {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        low
    }
}

}
