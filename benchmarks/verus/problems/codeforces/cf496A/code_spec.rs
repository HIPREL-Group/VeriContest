use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_gap_after_removal_at_pos(a: Seq<i32>, k: int, pos: int) -> int
        recommends
            1 <= k < a.len() - 1,
            0 <= pos <= a.len() - 1,
        decreases a.len() - 1 - pos,
    {
        if pos >= a.len() - 1 {
            0
        } else if pos == k - 1 {
            let gap = a[k + 1] - a[k - 1];
            let rest = if k + 1 < a.len() - 1 {
                Self::max_gap_after_removal_at_pos(a, k, k + 1)
            } else {
                0
            };
            if gap > rest {
                gap
            } else {
                rest
            }
        } else {
            let gap = a[pos + 1] - a[pos];
            let rest = Self::max_gap_after_removal_at_pos(a, k, pos + 1);
            if gap > rest {
                gap
            } else {
                rest
            }
        }
    }

    pub open spec fn max_gap_after_removal(a: Seq<i32>, k: int) -> int
        recommends
            1 <= k < a.len() - 1,
    {
        Self::max_gap_after_removal_at_pos(a, k, 0)
    }

    pub open spec fn min_max_difficulty_spec(a: Seq<i32>, k: int) -> int
        recommends
            a.len() >= 3,
            1 <= k <= a.len() - 1,
        decreases a.len() - 1 - k,
    {
        if k >= a.len() - 1 {
            Self::max_gap_after_removal(a, a.len() - 2)
        } else {
            let current = Self::max_gap_after_removal(a, k);
            let rest = Self::min_max_difficulty_spec(a, k + 1);
            if current < rest {
                current
            } else {
                rest
            }
        }
    }

    pub fn min_max_difficulty(a: Vec<i32>) -> (result: i32)
        requires
            a.len() >= 3,
            a.len() <= 100,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a@[i] <= 1000,
            forall |i: int| 0 <= i < a.len() - 1 ==> #[trigger] a@[i] < a@[i + 1],
        ensures
            forall |k: int| 1 <= k < a@.len() - 1 ==>
                #[trigger] Self::max_gap_after_removal(a@, k) >= result as int,
            exists |k: int| 1 <= k < a@.len() - 1 &&
                #[trigger] Self::max_gap_after_removal(a@, k) == result as int,
    {
        let n = a.len();
        let mut min_result = 10000;
        let mut k: usize = 1;
        while k < n - 1 {
            let mut max_gap = 0;
            let mut i: usize = 0;
            while i < n - 1 {
                let gap = if i == k - 1 {
                    a[k + 1] - a[k - 1]
                } else {
                    a[i + 1] - a[i]
                };
                if gap > max_gap {
                    max_gap = gap;
                }
                if i == k - 1 {
                    i = k + 1;
                } else {
                    i = i + 1;
                }
            }
            if max_gap < min_result {
                min_result = max_gap;
            }
            k = k + 1;
        }
        min_result
    }
}

}
