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

    proof fn lemma_window_sum_step(s: Seq<i32>, start: int, k: int)
        requires
            0 <= start,
            1 <= k,
            start + k <= s.len(),
        ensures
            Self::window_sum(s, start, k)
                == Self::window_sum(s, start, k - 1) + s[start + k - 1],
        decreases k,
    {
        if k == 1 {
            reveal_with_fuel(Solution::window_sum, 2);
        } else {
            reveal_with_fuel(Solution::window_sum, 2);
            Self::lemma_window_sum_step(s, start + 1, k - 1);
            assert(Self::window_sum(s, start + 1, k - 1)
                == Self::window_sum(s, start + 1, k - 2) + s[start + k - 1]);
        }
    }

    proof fn lemma_window_sum_slide(s: Seq<i32>, j: int, k: int)
        requires
            1 <= j,
            1 <= k,
            j + k <= s.len(),
        ensures
            Self::window_sum(s, j, k)
                == Self::window_sum(s, j - 1, k) - s[j - 1] + s[j + k - 1],
        decreases k,
    {
        Self::lemma_window_sum_step(s, j - 1, k);
        Self::lemma_window_sum_step(s, j, k);
    }

    proof fn lemma_window_sum_bounds(s: Seq<i32>, start: int, k: int)
        requires
            0 <= start,
            0 <= k,
            start + k <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 100,
        ensures
            0 <= Self::window_sum(s, start, k) <= 100 * k,
        decreases k,
    {
        if k == 0 {
        } else {
            reveal_with_fuel(Solution::window_sum, 2);
            Self::lemma_window_sum_bounds(s, start + 1, k - 1);
            let head = s[start] as int;
            let tail = Self::window_sum(s, start + 1, k - 1);
            assert(1 <= head <= 100);
            assert(0 <= tail <= 100 * (k - 1));
            assert(head >= 0);
            assert(head <= 100);
            assert(tail >= 0);
            assert(tail <= 100 * (k - 1));
            assert(0 <= head + tail) by (nonlinear_arith)
                requires
                    head >= 0,
                    tail >= 0;
            assert(head + tail <= 100 * k) by (nonlinear_arith)
                requires
                    head <= 100,
                    tail <= 100 * (k - 1),
                    k >= 1;
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
        while i < k
            invariant
                i <= k,
                n == heights.len(),
                1 <= k <= n <= 150_000,
                forall |j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights@[j] <= 100,
                sum as int == Self::window_sum(heights@, 0, i as int),
                0 <= sum as int <= 100 * i as int,
            decreases k - i,
        {
            let idx = i;
            proof {
                Self::lemma_window_sum_step(heights@, 0, idx as int + 1);
            }
            sum = sum + heights[idx] as i64;
            i = idx + 1;
            proof {
                assert(sum as int == Self::window_sum(heights@, 0, idx as int) + heights@[idx as int]);
                assert(Self::window_sum(heights@, 0, idx as int + 1)
                    == Self::window_sum(heights@, 0, idx as int) + heights@[idx as int]);
                assert(sum as int == Self::window_sum(heights@, 0, i as int));
                Self::lemma_window_sum_bounds(heights@, 0, i as int);
            }
        }
        let mut best_sum = sum;
        let mut best_start: usize = 0;
        let mut start: usize = 1;
        while start + k <= n
            invariant
                n == heights.len(),
                1 <= start <= n - k + 1,
                1 <= k <= n <= 150_000,
                forall |j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights@[j] <= 100,
                sum as int == Self::window_sum(heights@, start as int - 1, k as int),
                0 <= sum as int <= 100 * k as int,
                0 <= best_start < start,
                best_sum as int == Self::window_sum(heights@, best_start as int, k as int),
                0 <= best_sum as int <= 100 * k as int,
                forall |j: int| 0 <= j < start as int ==>
                    Self::window_sum(heights@, best_start as int, k as int)
                        <= #[trigger] Self::window_sum(heights@, j, k as int),
                forall |j: int| 0 <= j < best_start as int ==>
                    #[trigger] Self::window_sum(heights@, j, k as int)
                        > Self::window_sum(heights@, best_start as int, k as int),
            decreases n - k + 1 - start,
        {
            let prev_start = start;
            let prev_best_sum = best_sum;
            let prev_best_start = best_start;
            proof {
                Self::lemma_window_sum_slide(heights@, prev_start as int, k as int);
            }
            sum = sum - heights[prev_start - 1] as i64 + heights[prev_start + k - 1] as i64;
            proof {
                assert(sum as int == Self::window_sum(heights@, prev_start as int, k as int));
                Self::lemma_window_sum_bounds(heights@, prev_start as int, k as int);
            }
            if sum < best_sum {
                best_sum = sum;
                best_start = prev_start;
            }
            proof {
                if sum < prev_best_sum {
                    assert(best_start == prev_start);
                    assert(best_sum == sum);
                    assert(best_sum as int == Self::window_sum(heights@, best_start as int, k as int));
                    assert forall |j: int| 0 <= j < prev_start as int + 1 implies
                        Self::window_sum(heights@, best_start as int, k as int)
                            <= #[trigger] Self::window_sum(heights@, j, k as int) by {
                        if j < prev_start as int {
                            assert(Self::window_sum(heights@, prev_best_start as int, k as int)
                                <= Self::window_sum(heights@, j, k as int));
                            assert(Self::window_sum(heights@, best_start as int, k as int)
                                < Self::window_sum(heights@, prev_best_start as int, k as int));
                        } else {
                            assert(j == prev_start as int);
                        }
                    }
                    assert forall |j: int| 0 <= j < best_start as int implies
                        #[trigger] Self::window_sum(heights@, j, k as int)
                            > Self::window_sum(heights@, best_start as int, k as int) by {
                        assert(Self::window_sum(heights@, prev_best_start as int, k as int)
                            == prev_best_sum as int);
                        assert(Self::window_sum(heights@, prev_best_start as int, k as int)
                            > Self::window_sum(heights@, best_start as int, k as int));
                        assert(Self::window_sum(heights@, prev_best_start as int, k as int)
                            <= Self::window_sum(heights@, j, k as int));
                    }
                } else {
                    assert(best_start == prev_best_start);
                    assert(best_sum == prev_best_sum);
                    assert(best_sum as int == Self::window_sum(heights@, best_start as int, k as int));
                    assert forall |j: int| 0 <= j < prev_start as int + 1 implies
                        Self::window_sum(heights@, best_start as int, k as int)
                            <= #[trigger] Self::window_sum(heights@, j, k as int) by {
                        if j < prev_start as int {
                        } else {
                            assert(j == prev_start as int);
                            assert(Self::window_sum(heights@, best_start as int, k as int)
                                == best_sum as int);
                            assert(best_sum as int <= sum as int);
                            assert(sum as int == Self::window_sum(heights@, prev_start as int, k as int));
                        }
                    }
                    assert forall |j: int| 0 <= j < best_start as int implies
                        #[trigger] Self::window_sum(heights@, j, k as int)
                            > Self::window_sum(heights@, best_start as int, k as int) by {
                    }
                }
            }
            start = prev_start + 1;
        }
        proof {
            assert(start == n - k + 1) by (nonlinear_arith)
                requires
                    start <= n - k + 1,
                    start + k > n,
                    k <= n;
            assert(best_start < start);
        }
        best_start + 1
    }
}

}
