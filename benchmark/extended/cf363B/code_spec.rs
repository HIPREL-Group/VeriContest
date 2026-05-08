use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(s: Seq<i32>, start: int, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            s[start] + Self::window_sum(s, start + 1, k - 1)
        }
    }

    pub fn min_sum_window_start(heights: Vec<i32>, k: usize) -> (result: usize)
        requires
            heights.len() <= 150_000,
            1 <= k <= heights.len(),
            forall |i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights@[i] <= 100,
        ensures
            1 <= result <= heights.len() - k + 1,
            forall |i: int| 0 <= i <= heights@.len() - k as int ==>
                Self::window_sum(heights@, result as int - 1, k as int)
                    <= #[trigger] Self::window_sum(heights@, i, k as int),
            forall |i: int| 0 <= i < result as int - 1 ==>
                #[trigger] Self::window_sum(heights@, i, k as int)
                    > Self::window_sum(heights@, result as int - 1, k as int),
    {
        let n = heights.len();
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < k {
            let idx = i;
            sum = sum + heights[idx] as i64;
            i = idx + 1;
        }
        let mut best_sum = sum;
        let mut best_start: usize = 0;
        let mut start: usize = 1;
        while start + k <= n {
            let prev_start = start;
            let prev_best_sum = best_sum;
            let prev_best_start = best_start;
            sum = sum - heights[prev_start - 1] as i64 + heights[prev_start + k - 1] as i64;
            if sum < best_sum {
                best_sum = sum;
                best_start = prev_start;
            }
            start = prev_start + 1;
        }
        best_start + 1
    }
}

}
