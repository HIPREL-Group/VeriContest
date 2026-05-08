use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_range(s: Seq<i64>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= s.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            s[l] as int + Self::sum_range(s, l + 1, r)
        }
    }

    pub open spec fn min_white_windows(s: Seq<i64>, k: int, processed: int) -> int
        recommends
            1 <= k <= s.len(),
            0 <= processed <= s.len() - k + 1,
        decreases processed,
    {
        if processed <= 0 {
            k
        } else {
            let prev = Self::min_white_windows(s, k, processed - 1);
            let start = processed - 1;
            let here = Self::sum_range(s, start, start + k);
            if here < prev {
                here
            } else {
                prev
            }
        }
    }

    pub open spec fn valid_window_start(n: int, k: int, start: int) -> bool {
        0 <= start <= n - k
    }

    pub open spec fn whites_in_window(s: Seq<i64>, start: int, k: int) -> int
        recommends
            0 <= start,
            start + k <= s.len(),
    {
        Self::sum_range(s, start, start + k)
    }

    proof fn lemma_sum_range_nonneg(s: Seq<i64>, l: int, r: int)
        requires
            0 <= l <= r <= s.len(),
            forall|i: int| l <= i < r ==> 0 <= #[trigger] s[i],
        ensures
            0 <= Self::sum_range(s, l, r),
        decreases r - l,
    {
        if l < r {
            Self::lemma_sum_range_nonneg(s, l + 1, r);
        }
    }

    proof fn lemma_sum_range_le_len(s: Seq<i64>, l: int, r: int)
        requires
            0 <= l <= r <= s.len(),
            forall|i: int| l <= i < r ==> #[trigger] s[i] <= 1,
        ensures
            Self::sum_range(s, l, r) <= r - l,
        decreases r - l,
    {
        if l < r {
            Self::lemma_sum_range_le_len(s, l + 1, r);
            assert(Self::sum_range(s, l, r) == s[l] as int + Self::sum_range(s, l + 1, r));
            assert(s[l] as int <= 1);
            assert(Self::sum_range(s, l + 1, r) <= r - (l + 1));
            assert(Self::sum_range(s, l, r) <= 1 + (r - (l + 1)));
        }
    }

    proof fn lemma_sum_range_extend_right(s: Seq<i64>, l: int, r: int)
        requires
            0 <= l <= r < s.len(),
        ensures
            Self::sum_range(s, l, r + 1) == Self::sum_range(s, l, r) + s[r] as int,
        decreases r - l,
    {
        if l == r {
            assert(Self::sum_range(s, l, r + 1) == s[l] as int + Self::sum_range(s, l + 1, r + 1));
            assert(Self::sum_range(s, l + 1, r + 1) == 0);
            assert(Self::sum_range(s, l, r) == 0);
        } else {
            Self::lemma_sum_range_extend_right(s, l + 1, r);
            assert(Self::sum_range(s, l, r + 1) == s[l] as int + Self::sum_range(s, l + 1, r + 1));
            assert(Self::sum_range(s, l, r) == s[l] as int + Self::sum_range(s, l + 1, r));
        }
    }

    proof fn lemma_min_white_windows_lower_bound(s: Seq<i64>, k: int, processed: int, start: int)
        requires
            1 <= k <= s.len(),
            0 <= processed <= s.len() - k + 1,
            0 <= start < processed,
        ensures
            Self::min_white_windows(s, k, processed) <= Self::sum_range(s, start, start + k),
        decreases processed,
    {
        if processed > 0 {
            let prev = Self::min_white_windows(s, k, processed - 1);
            let here = Self::sum_range(s, processed - 1, processed - 1 + k);
            if start == processed - 1 {
                if here < prev {
                    assert(Self::min_white_windows(s, k, processed) == here);
                } else {
                    assert(Self::min_white_windows(s, k, processed) == prev);
                    assert(prev <= here);
                }
            } else {
                Self::lemma_min_white_windows_lower_bound(s, k, processed - 1, start);
                assert(prev <= Self::sum_range(s, start, start + k));
                if here < prev {
                    assert(Self::min_white_windows(s, k, processed) == here);
                    assert(here <= prev);
                } else {
                    assert(Self::min_white_windows(s, k, processed) == prev);
                }
            }
        }
    }

    proof fn lemma_min_white_windows_witness(s: Seq<i64>, k: int, processed: int) -> (start: int)
        requires
            1 <= k <= s.len(),
            1 <= processed <= s.len() - k + 1,
            forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] <= 1,
        ensures
            0 <= start < processed,
            Self::min_white_windows(s, k, processed) == Self::sum_range(s, start, start + k),
        decreases processed,
    {
        if processed == 1 {
            reveal_with_fuel(Solution::min_white_windows, 2);
            Self::lemma_sum_range_le_len(s, 0, k);
            assert(Self::sum_range(s, 0, k) <= k);
            assert(Self::min_white_windows(s, k, 1) == Self::sum_range(s, 0, k));
            0
        } else {
            reveal_with_fuel(Solution::min_white_windows, 2);
            let st_prev = Self::lemma_min_white_windows_witness(s, k, processed - 1);
            let prev = Self::min_white_windows(s, k, processed - 1);
            let here = Self::sum_range(s, processed - 1, processed - 1 + k);
            if here < prev {
                assert(Self::min_white_windows(s, k, processed) == here);
                processed - 1
            } else {
                assert(0 <= st_prev < processed - 1);
                assert(Self::min_white_windows(s, k, processed - 1) == Self::sum_range(s, st_prev, st_prev + k));
                assert(Self::min_white_windows(s, k, processed) == prev);
                assert(Self::min_white_windows(s, k, processed) == Self::sum_range(s, st_prev, st_prev + k));
                st_prev
            }
        }
    }

    pub fn min_recolors(n: usize, k: usize, s: Vec<i64>) -> (result: usize)
        requires
            1 <= n,
            n <= 200000,
            1 <= k <= n,
            s.len() == n,
            forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
        ensures
            exists|start: int|
                Self::valid_window_start(n as int, k as int, start)
                    && result as int == Self::whites_in_window(s@, start, k as int),
            forall|start: int|
                Self::valid_window_start(n as int, k as int, start)
                    ==> result as int <= Self::whites_in_window(s@, start, k as int),
    {
        let mut cur: i64 = 0;
        let mut j: usize = 0;
        while j < k
            invariant
                0 <= j <= k,
                k <= n,
                n == s.len(),
                n <= 200000,
                forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
                cur as int == Self::sum_range(s@, 0, j as int),
                0 <= cur,
                cur <= j as i64,
            decreases k - j,
        {
            if j > 0 {
                proof {
                    Self::lemma_sum_range_extend_right(s@, 0, j as int - 1);
                }
            }
            proof {
                assert(0 <= s@[j as int] <= 1);
                assert(cur + s@[j as int] <= 200001);
            }
            cur = cur + s[j];
            j += 1;
            proof {
                if j == 1 {
                    assert(Self::sum_range(s@, 0, 1) == s@[0] as int + Self::sum_range(s@, 1, 1));
                    assert(Self::sum_range(s@, 1, 1) == 0);
                } else {
                    Self::lemma_sum_range_extend_right(s@, 0, j as int - 1);
                    assert(Self::sum_range(s@, 0, j as int)
                        == Self::sum_range(s@, 0, j as int - 1) + s@[j as int - 1] as int);
                }
            }
        }

        let mut best: i64 = cur;
        let mut left: usize = 0;

        proof {
            reveal_with_fuel(Solution::min_white_windows, 2);
            Self::lemma_sum_range_le_len(s@, 0, k as int);
            assert(Self::sum_range(s@, 0, k as int) <= k as int);
            assert(best as int == Self::min_white_windows(s@, k as int, 1));
        }

        while left + k < n
            invariant
                0 <= left,
                left + k <= n,
                n == s.len(),
                n <= 200000,
                1 <= k <= n,
                forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
                cur as int == Self::sum_range(s@, left as int, left as int + k as int),
                0 <= cur <= k as i64,
                0 <= best <= k as i64,
                best as int == Self::min_white_windows(s@, k as int, left as int + 1),
            decreases n - (left + k),
        {
            proof {
                assert(left + k < n);
                assert(Self::sum_range(s@, left as int, left as int + k as int)
                    == s@[left as int] as int + Self::sum_range(s@, left as int + 1, left as int + k as int));
                Self::lemma_sum_range_nonneg(s@, left as int + 1, left as int + k as int);
                Self::lemma_sum_range_le_len(s@, left as int + 1, left as int + k as int);
                Self::lemma_sum_range_extend_right(s@, left as int + 1, left as int + k as int);
                assert(Self::sum_range(s@, left as int + 1, left as int + k as int + 1)
                    == Self::sum_range(s@, left as int + 1, left as int + k as int)
                        + s@[left as int + k as int] as int);
                assert(Self::sum_range(s@, left as int + 1, left as int + k as int + 1)
                    == Self::sum_range(s@, left as int, left as int + k as int)
                        - s@[left as int] as int + s@[left as int + k as int] as int);
                assert(0 <= Self::sum_range(s@, left as int + 1, left as int + k as int));
                assert(Self::sum_range(s@, left as int + 1, left as int + k as int) <= k as int - 1);
                assert(0 <= s@[left as int + k as int] <= 1);
                assert(0 <= cur - s@[left as int] + s@[left as int + k as int]);
                assert(cur - s@[left as int] + s@[left as int + k as int] <= k as int);
            }

            let next = cur - s[left] + s[left + k];
            cur = next;
            left += 1;
            let old_best = best;
            if cur < best {
                best = cur;
            }

            proof {
                assert(cur as int == Self::sum_range(s@, left as int, left as int + k as int));
                assert(old_best as int == Self::min_white_windows(s@, k as int, left as int));
                assert(Self::min_white_windows(s@, k as int, left as int + 1)
                    == if Self::sum_range(s@, left as int, left as int + k as int)
                        < Self::min_white_windows(s@, k as int, left as int)
                    {
                        Self::sum_range(s@, left as int, left as int + k as int)
                    } else {
                        Self::min_white_windows(s@, k as int, left as int)
                    });
                assert(best as int == Self::min_white_windows(s@, k as int, left as int + 1));
            }
        }

        proof {
            assert(best as int == Self::min_white_windows(s@, k as int, n as int - k as int + 1));
            assert forall|i: int| 0 <= i < s@.len() implies 0 <= #[trigger] s@[i] <= 1 by {
                assert(s@[i] == 0 || s@[i] == 1);
            }
            let st = Self::lemma_min_white_windows_witness(s@, k as int, n as int - k as int + 1);
            assert(Self::valid_window_start(n as int, k as int, st));
            assert(best as int == Self::whites_in_window(s@, st, k as int));

            assert forall|start: int|
                Self::valid_window_start(n as int, k as int, start)
                    implies best as int <= Self::whites_in_window(s@, start, k as int) by {
                assert(0 <= start < n as int - k as int + 1);
                Self::lemma_min_white_windows_lower_bound(s@, k as int, n as int - k as int + 1, start);
                assert(best as int == Self::min_white_windows(s@, k as int, n as int - k as int + 1));
            }
        }

        best as usize
    }

}

}
