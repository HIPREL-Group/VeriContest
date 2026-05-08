use vstd::prelude::*;
fn main() {}
verus! {
pub struct Solution;
impl Solution {
    
    
    

    
    pub open spec fn sum_range_spec(nums: Seq<i32>, lo: int, hi: int) -> int
        decreases hi - lo
    {
        if hi <= lo { 0 }
        else { Self::sum_range_spec(nums, lo, hi - 1) + nums[hi - 1] as int }
    }

    
    pub open spec fn is_valid_split_spec(n: int, k: int, cuts: Seq<int>) -> bool {
        k >= 1
        && cuts.len() == k + 1
        && cuts[0] == 0
        && cuts[k as int] == n
        && forall|i: int|
            #![trigger cuts[i]]
            #![trigger cuts[i + 1]]
            0 <= i < k ==> cuts[i] < cuts[i + 1]
    }

    
    pub open spec fn max_segment_sum_spec(nums: Seq<i32>, k: int, cuts: Seq<int>) -> int
        decreases k
    {
        if k <= 1 {
            Self::sum_range_spec(nums, cuts[0], cuts[1])
        } else {
            let prev = Self::max_segment_sum_spec(nums, k - 1, cuts);
            let last = Self::sum_range_spec(nums, cuts[k - 1], cuts[k as int]);
            if last > prev { last } else { prev }
        }
    }

    
    pub open spec fn greedy_count_spec(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    ) -> int
        decreases nums.len() - i
    {
        if i >= nums.len() { 1 }
        else if current_sum + nums[i] as int > max_sum {
            1 + Self::greedy_count_spec(nums, max_sum, i + 1, nums[i] as int)
        } else {
            Self::greedy_count_spec(nums, max_sum, i + 1, current_sum + nums[i] as int)
        }
    }

    
    pub open spec fn max_elem_spec(nums: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else {
            let prev = Self::max_elem_spec(nums, end - 1);
            if nums[end - 1] as int > prev { nums[end - 1] as int } else { prev }
        }
    }

    pub open spec fn greedy_cuts_spec(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    ) -> Seq<int>
        decreases nums.len() - i
    {
        if i >= nums.len() {
            seq![nums.len() as int]
        } else if current_sum + nums[i] as int > max_sum {
            seq![i as int] + Self::greedy_cuts_spec(nums, max_sum, i + 1, nums[i] as int)
        } else {
            Self::greedy_cuts_spec(nums, max_sum, i + 1, current_sum + nums[i] as int)
        }
    }

    
    
    

    proof fn lemma_sum_range_nonneg(nums: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo <= hi <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
        ensures
            Self::sum_range_spec(nums, lo, hi) >= 0,
        decreases hi - lo,
    {
        if lo < hi {
            Self::lemma_sum_range_nonneg(nums, lo, hi - 1);
        }
    }

    proof fn lemma_sum_range_split(nums: Seq<i32>, a: int, b: int, c: int)
        requires 0 <= a <= b <= c <= nums.len(),
        ensures
            Self::sum_range_spec(nums, a, c)
                == Self::sum_range_spec(nums, a, b) + Self::sum_range_spec(nums, b, c),
        decreases c - b,
    {
        if b < c {
            Self::lemma_sum_range_split(nums, a, b, c - 1);
        }
    }

    proof fn lemma_sum_range_first(nums: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo < hi <= nums.len(),
        ensures
            Self::sum_range_spec(nums, lo, hi)
                == nums[lo] as int + Self::sum_range_spec(nums, lo + 1, hi),
        decreases hi - lo,
    {
        if hi == lo + 1 {
            assert(Self::sum_range_spec(nums, lo, lo) == 0);
            assert(Self::sum_range_spec(nums, lo + 1, lo + 1) == 0);
        } else {
            Self::lemma_sum_range_first(nums, lo, hi - 1);
        }
    }

    proof fn lemma_sum_range_bounded(nums: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo <= hi <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            nums.len() <= 1_000,
        ensures
            Self::sum_range_spec(nums, lo, hi) <= (hi - lo) * 1_000_000,
        decreases hi - lo,
    {
        if lo < hi {
            Self::lemma_sum_range_bounded(nums, lo, hi - 1);
        }
    }

    
    
    

    proof fn lemma_max_nonneg(nums: Seq<i32>, end: int)
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            0 <= end <= nums.len(),
        ensures Self::max_elem_spec(nums, end) >= 0,
        decreases end,
    {
        if end > 0 { Self::lemma_max_nonneg(nums, end - 1); }
    }

    proof fn lemma_max_le_sum(nums: Seq<i32>, end: int)
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            0 <= end <= nums.len(),
        ensures
            Self::max_elem_spec(nums, end) <= Self::sum_range_spec(nums, 0, end),
        decreases end,
    {
        if end > 0 {
            Self::lemma_max_le_sum(nums, end - 1);
            Self::lemma_sum_range_nonneg(nums, 0, end - 1);
        }
    }

    proof fn lemma_max_bounded(nums: Seq<i32>, end: int)
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            0 <= end <= nums.len(),
        ensures Self::max_elem_spec(nums, end) <= 1_000_000,
        decreases end,
    {
        if end > 0 { Self::lemma_max_bounded(nums, end - 1); }
    }

    proof fn lemma_max_is_bound(nums: Seq<i32>, end: int, j: int)
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            0 <= end <= nums.len(),
            0 <= j < end,
        ensures nums[j] as int <= Self::max_elem_spec(nums, end),
        decreases end,
    {
        if j < end - 1 {
            Self::lemma_max_is_bound(nums, end - 1, j);
        }
    }

    
    
    

    proof fn lemma_cuts_lower_bound(n: int, k: int, cuts: Seq<int>, j: int)
        requires
            Self::is_valid_split_spec(n, k, cuts),
            0 <= j <= k,
        ensures
            cuts[j as int] >= j,
        decreases j,
    {
        if j > 0 {
            Self::lemma_cuts_lower_bound(n, k, cuts, j - 1);
        }
    }

    proof fn lemma_cuts_upper_bound(n: int, k: int, cuts: Seq<int>, j: int)
        requires
            Self::is_valid_split_spec(n, k, cuts),
            0 <= j <= k,
        ensures
            cuts[j as int] <= n,
        decreases k - j,
    {
        if j < k {
            Self::lemma_cuts_upper_bound(n, k, cuts, j + 1);
        }
    }

    proof fn lemma_cuts_in_range(n: int, k: int, cuts: Seq<int>, j: int)
        requires
            Self::is_valid_split_spec(n, k, cuts),
            0 <= j <= k,
        ensures
            0 <= cuts[j as int] <= n,
    {
        Self::lemma_cuts_lower_bound(n, k, cuts, j);
        Self::lemma_cuts_upper_bound(n, k, cuts, j);
    }

    
    
    

    proof fn lemma_greedy_count_pos(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    )
        requires 0 <= i <= nums.len(),
        ensures Self::greedy_count_spec(nums, max_sum, i, current_sum) >= 1,
        decreases nums.len() - i,
    {
        if i < nums.len() {
            if current_sum + nums[i] as int > max_sum {
                Self::lemma_greedy_count_pos(nums, max_sum, i + 1, nums[i] as int);
            } else {
                Self::lemma_greedy_count_pos(nums, max_sum, i + 1, current_sum + nums[i] as int);
            }
        }
    }

    proof fn lemma_greedy_count_bounded(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    )
        requires 0 <= i <= nums.len(),
        ensures Self::greedy_count_spec(nums, max_sum, i, current_sum) <= nums.len() - i + 1,
        decreases nums.len() - i,
    {
        if i < nums.len() {
            if current_sum + nums[i] as int > max_sum {
                Self::lemma_greedy_count_bounded(nums, max_sum, i + 1, nums[i] as int);
            } else {
                Self::lemma_greedy_count_bounded(nums, max_sum, i + 1, current_sum + nums[i] as int);
            }
        }
    }

    
    
    

    proof fn lemma_greedy_no_split(
        nums: Seq<i32>, max_sum: int, start: int, end: int, current_sum: int,
    )
        requires
            0 <= start <= end <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            current_sum >= 0,
            current_sum + Self::sum_range_spec(nums, start, end) <= max_sum,
        ensures
            Self::greedy_count_spec(nums, max_sum, start, current_sum)
                == Self::greedy_count_spec(
                    nums, max_sum, end,
                    current_sum + Self::sum_range_spec(nums, start, end),
                ),
        decreases end - start,
    {
        if start < end {
            Self::lemma_sum_range_first(nums, start, end);
            Self::lemma_sum_range_nonneg(nums, start + 1, end);
            Self::lemma_greedy_no_split(
                nums, max_sum, start + 1, end, current_sum + nums[start] as int,
            );
        }
    }

    
    
    

    proof fn lemma_greedy_segment(
        nums: Seq<i32>, max_sum: int, seg_start: int, seg_end: int, current_sum: int,
    ) -> (new_cs: int)
        requires
            0 <= seg_start < seg_end <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            Self::sum_range_spec(nums, seg_start, seg_end) <= max_sum,
            current_sum >= 0,
            current_sum + Self::sum_range_spec(nums, seg_start, seg_end) > max_sum,
        ensures
            0 <= new_cs,
            new_cs <= Self::sum_range_spec(nums, seg_start, seg_end),
            Self::greedy_count_spec(nums, max_sum, seg_start, current_sum)
                == 1 + Self::greedy_count_spec(nums, max_sum, seg_end, new_cs),
        decreases seg_end - seg_start,
    {
        Self::lemma_sum_range_first(nums, seg_start, seg_end);
        Self::lemma_sum_range_nonneg(nums, seg_start + 1, seg_end);
        if current_sum + nums[seg_start] as int > max_sum {
            Self::lemma_greedy_no_split(
                nums, max_sum, seg_start + 1, seg_end, nums[seg_start] as int,
            );
            nums[seg_start] as int + Self::sum_range_spec(nums, seg_start + 1, seg_end)
        } else {
            if seg_start + 1 == seg_end {
                assert(false);
                0  
            } else {
                let inner = Self::lemma_greedy_segment(
                    nums, max_sum, seg_start + 1, seg_end,
                    current_sum + nums[seg_start] as int,
                );
                assert(0 <= inner <= Self::sum_range_spec(nums, seg_start, seg_end));
                inner
            }
        }
    }

    
    
    

    proof fn lemma_greedy_optimal_from_seg(
        nums: Seq<i32>, max_sum: int, k: int, cuts: Seq<int>,
        seg: int, current_sum: int,
    )
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            Self::is_valid_split_spec(nums.len() as int, k, cuts),
            forall|j: int|
                #![trigger cuts[j]]
                #![trigger cuts[j + 1]]
                0 <= j < k ==> Self::sum_range_spec(nums, cuts[j], cuts[j + 1]) <= max_sum,
            1 <= seg <= k,
            0 <= current_sum <= max_sum,
            max_sum >= 0,
        ensures
            Self::greedy_count_spec(nums, max_sum, cuts[seg as int], current_sum)
                <= k - seg + 1,
        decreases k - seg,
    {
        Self::lemma_cuts_in_range(nums.len() as int, k, cuts, seg);
        if seg == k {
        } else {
            Self::lemma_cuts_in_range(nums.len() as int, k, cuts, seg + 1);
            assert(Self::sum_range_spec(nums, cuts[seg as int], cuts[seg + 1]) <= max_sum);
            if current_sum + Self::sum_range_spec(nums, cuts[seg as int], cuts[seg + 1]) <= max_sum {
                Self::lemma_sum_range_nonneg(nums, cuts[seg as int], cuts[seg + 1]);
                Self::lemma_greedy_no_split(
                    nums, max_sum, cuts[seg as int], cuts[seg + 1], current_sum,
                );
                let new_cs = current_sum + Self::sum_range_spec(nums, cuts[seg as int], cuts[seg + 1]);
                assert(Self::sum_range_spec(nums, cuts[seg as int], cuts[seg + 1]) >= 0);
                assert(current_sum >= 0);
                assert(new_cs >= 0);
                Self::lemma_greedy_optimal_from_seg(nums, max_sum, k, cuts, seg + 1, new_cs);
            } else {
                let new_cs = Self::lemma_greedy_segment(
                    nums, max_sum, cuts[seg as int], cuts[seg + 1], current_sum,
                );
                assert(0 <= new_cs);  
                let seg_sum = Self::sum_range_spec(nums, cuts[seg as int], cuts[seg + 1]);
                assert(new_cs <= seg_sum);
                assert(seg_sum <= max_sum);
                assert(new_cs <= max_sum);
                Self::lemma_greedy_optimal_from_seg(nums, max_sum, k, cuts, seg + 1, new_cs);
            }
        }
    }

    
    
    

    proof fn lemma_greedy_optimal(
        nums: Seq<i32>, max_sum: int, k: int, cuts: Seq<int>,
    )
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            Self::is_valid_split_spec(nums.len() as int, k, cuts),
            forall|j: int|
                #![trigger cuts[j]]
                #![trigger cuts[j + 1]]
                0 <= j < k
                ==> Self::sum_range_spec(nums, cuts[j], cuts[j + 1]) <= max_sum,
            max_sum >= 0,
        ensures
            Self::greedy_count_spec(nums, max_sum, 0, 0) <= k,
    {
        Self::lemma_cuts_in_range(nums.len() as int, k, cuts, 0);
        Self::lemma_cuts_in_range(nums.len() as int, k, cuts, 1);
        assert(Self::sum_range_spec(nums, cuts[0], cuts[1 as int]) <= max_sum);
        Self::lemma_sum_range_nonneg(nums, 0, cuts[1 as int]);
        Self::lemma_greedy_no_split(nums, max_sum, 0, cuts[1 as int], 0);
        let cs1 = Self::sum_range_spec(nums, 0, cuts[1 as int]);
        Self::lemma_greedy_optimal_from_seg(nums, max_sum, k, cuts, 1, cs1);
    }

    
    
    

    proof fn lemma_max_seg_ge_each(
        nums: Seq<i32>, k: int, cuts: Seq<int>, j: int,
    )
        requires
            k >= 1,
            cuts.len() >= k + 1,
            0 <= j < k,
        ensures
            Self::max_segment_sum_spec(nums, k, cuts)
                >= Self::sum_range_spec(nums, cuts[j], cuts[j + 1]),
        decreases k,
    {
        if k <= 1 {
        } else if j == k - 1 {
        } else {
            Self::lemma_max_seg_ge_each(nums, k - 1, cuts, j);
        }
    }

    proof fn lemma_max_seg_le_bound(
        nums: Seq<i32>, k: int, cuts: Seq<int>, bound: int,
    )
        requires
            k >= 1,
            cuts.len() >= k + 1,
            forall|j: int|
                #![trigger cuts[j]]
                #![trigger cuts[j + 1]]
                0 <= j < k
                ==> Self::sum_range_spec(nums, cuts[j], cuts[j + 1]) <= bound,
        ensures
            Self::max_segment_sum_spec(nums, k, cuts) <= bound,
        decreases k,
    {
        if k <= 1 {
        } else {
            Self::lemma_max_seg_le_bound(nums, k - 1, cuts, bound);
        }
    }

    
    
    

    proof fn lemma_greedy_cuts_len(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    )
        requires 0 <= i <= nums.len(),
        ensures
            Self::greedy_cuts_spec(nums, max_sum, i, current_sum).len()
                == Self::greedy_count_spec(nums, max_sum, i, current_sum),
        decreases nums.len() - i,
    {
        if i < nums.len() {
            if current_sum + nums[i] as int > max_sum {
                Self::lemma_greedy_cuts_len(nums, max_sum, i + 1, nums[i] as int);
            } else {
                Self::lemma_greedy_cuts_len(nums, max_sum, i + 1, current_sum + nums[i] as int);
            }
        }
    }

    
    
    

    proof fn lemma_greedy_cuts_all_props(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    )
        requires
            0 <= i <= nums.len(),
            forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j],
            forall|j: int| 0 <= j < nums.len() ==> nums[j] as int <= max_sum,
            0 <= current_sum <= max_sum,
            max_sum >= 0,
        ensures ({
            let gc = Self::greedy_cuts_spec(nums, max_sum, i, current_sum);
            let g = Self::greedy_count_spec(nums, max_sum, i, current_sum);
            &&& gc.len() == g
            &&& g >= 1
            &&& gc[g - 1] == nums.len() as int
            &&& (forall|a: int| 0 <= a < g ==> i <= #[trigger] gc[a] <= nums.len() as int)
            &&& (i < nums.len() as int && current_sum + nums[i] as int <= max_sum
                ==> gc[0] > i)
            &&& (forall|a: int| 0 <= a < g - 1 ==> gc[a] < #[trigger] gc[a + 1])
            &&& current_sum + Self::sum_range_spec(nums, i, gc[0]) <= max_sum
            &&& (forall|a: int| 0 <= a < g - 1
                ==> Self::sum_range_spec(nums, gc[a], #[trigger] gc[a + 1]) <= max_sum)
        }),
        decreases nums.len() - i,
    {
        Self::lemma_greedy_cuts_len(nums, max_sum, i, current_sum);
        Self::lemma_greedy_count_pos(nums, max_sum, i, current_sum);

        if i >= nums.len() as int {
        } else if current_sum + nums[i] as int > max_sum {
            Self::lemma_greedy_cuts_all_props(nums, max_sum, i + 1, nums[i] as int);
            let tail = Self::greedy_cuts_spec(nums, max_sum, i + 1, nums[i] as int);
            let g_tail = Self::greedy_count_spec(nums, max_sum, i + 1, nums[i] as int);
            let gc = seq![i as int] + tail;
            let g = 1 + g_tail;

            assert(gc[0] == i);
            assert forall|a: int| 1 <= a < g implies gc[a] == tail[a - 1] by {
                assert(gc[a] == (seq![i as int] + tail)[a]);
            };

            assert forall|a: int| 0 <= a < g implies i <= #[trigger] gc[a] <= nums.len() as int by {
                if a == 0 {} else { assert(gc[a] == tail[a - 1]); }
            };

            assert(tail[0] >= i + 1);
            assert forall|a: int| 0 <= a < g - 1 implies gc[a] < #[trigger] gc[a + 1] by {
                if a == 0 {
                    assert(gc[0] == i);
                    assert(gc[1 as int] == tail[0]);
                } else {
                    
                    let b = a - 1;
                    assert(0 <= b && b < g_tail - 1);
                    assert(tail[b] < tail[b + 1]);
                }
            };

            assert(Self::sum_range_spec(nums, i, gc[0]) == 0);

            assert forall|a: int| 0 <= a < g - 1
                implies Self::sum_range_spec(nums, gc[a], #[trigger] gc[a + 1]) <= max_sum
            by {
                if a == 0 {
                    assert(gc[0] == i);
                    assert(gc[1 as int] == tail[0]);
                    Self::lemma_sum_range_first(nums, i, tail[0]);
                } else {
                    let b = a - 1;
                    assert(Self::sum_range_spec(nums, tail[b], tail[b + 1]) <= max_sum);
                }
            };
        } else {
            Self::lemma_greedy_cuts_all_props(
                nums, max_sum, i + 1, current_sum + nums[i] as int,
            );
            let gc = Self::greedy_cuts_spec(nums, max_sum, i + 1, current_sum + nums[i] as int);
            let g = Self::greedy_count_spec(nums, max_sum, i + 1, current_sum + nums[i] as int);
            assert(gc[0] >= i + 1);
            assert(gc[0] <= nums.len() as int);
            Self::lemma_sum_range_first(nums, i, gc[0]);
        }
    }

    
    
    

    proof fn lemma_greedy_produces_valid_split(
        nums: Seq<i32>, max_sum: int,
    )
        requires
            nums.len() >= 1,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            max_sum >= Self::max_elem_spec(nums, nums.len() as int),
            max_sum >= 0,
        ensures ({
            let g = Self::greedy_count_spec(nums, max_sum, 0, 0);
            let full_cuts = seq![0int] + Self::greedy_cuts_spec(nums, max_sum, 0, 0);
            g >= 1
            && Self::is_valid_split_spec(nums.len() as int, g, full_cuts)
            && forall|j: int|
                #![trigger full_cuts[j]]
                #![trigger full_cuts[j + 1]]
                0 <= j < g
                ==> Self::sum_range_spec(nums, full_cuts[j], full_cuts[j + 1]) <= max_sum
        }),
    {
        assert forall|j: int| 0 <= j < nums.len()
            implies nums[j] as int <= max_sum
        by {
            Self::lemma_max_is_bound(nums, nums.len() as int, j);
        };

        Self::lemma_max_nonneg(nums, nums.len() as int);
        Self::lemma_greedy_cuts_all_props(nums, max_sum, 0, 0);

        let gc = Self::greedy_cuts_spec(nums, max_sum, 0, 0);
        let g = Self::greedy_count_spec(nums, max_sum, 0, 0);
        let full = seq![0int] + gc;

        assert(full.len() == g + 1);
        assert(full[0] == 0);

        assert forall|idx: int| 1 <= idx < g + 1 implies full[idx] == gc[idx - 1] by {
            assert(full[idx] == (seq![0int] + gc)[idx]);
        };
        assert(full[g as int] == gc[g - 1]);

        assert forall|i: int|
            #![trigger full[i]]
            #![trigger full[i + 1]]
            0 <= i < g implies full[i] < full[i + 1]
        by {
            if i == 0 {
                assert(full[0] == 0);
                assert(full[1 as int] == gc[0]);
            } else {
                
                let b = i - 1;
                assert(0 <= b && b < g - 1);
                assert(gc[b] < gc[b + 1]);
            }
        };

        assert forall|j: int|
            #![trigger full[j]]
            #![trigger full[j + 1]]
            0 <= j < g
            implies Self::sum_range_spec(nums, full[j], full[j + 1]) <= max_sum
        by {
            if j == 0 {
                assert(full[0] == 0);
                assert(full[1 as int] == gc[0]);
            } else {
                let b = j - 1;
                assert(Self::sum_range_spec(nums, gc[b], gc[b + 1]) <= max_sum);
            }
        };
    }

    
    
    

    proof fn lemma_refine_split(
        nums: Seq<i32>, g: int, k: int, max_bound: int, cuts: Seq<int>,
    )
        requires
            1 <= g <= k,
            k <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            Self::is_valid_split_spec(nums.len() as int, g, cuts),
            forall|j: int|
                #![trigger cuts[j]]
                #![trigger cuts[j + 1]]
                0 <= j < g
                ==> Self::sum_range_spec(nums, cuts[j], cuts[j + 1]) <= max_bound,
        ensures
            exists|new_cuts: Seq<int>|
                Self::is_valid_split_spec(nums.len() as int, k, new_cuts)
                && #[trigger] Self::max_segment_sum_spec(nums, k, new_cuts) <= max_bound,
        decreases k - g,
    {
        if g == k {
            Self::lemma_max_seg_le_bound(nums, k, cuts, max_bound);
        } else {
            Self::lemma_find_big_segment(nums.len() as int, g, cuts);
            let j: int = choose|j: int| 0 <= j < g && #[trigger] cuts[j + 1] - cuts[j] >= 2;

            let left_part = cuts.subrange(0, j + 1);
            let mid_val = seq![cuts[j as int] + 1];
            let right_part = cuts.subrange(j + 1, cuts.len() as int);
            let new_cuts = left_part + mid_val + right_part;

            Self::lemma_inserted_split_valid(nums, g, cuts, j, new_cuts);
            Self::lemma_inserted_split_sums_bounded(nums, g, cuts, j, new_cuts, max_bound);
            Self::lemma_refine_split(nums, g + 1, k, max_bound, new_cuts);
        }
    }

    proof fn lemma_find_big_segment(n: int, g: int, cuts: Seq<int>)
        requires
            Self::is_valid_split_spec(n, g, cuts),
            n > g,
        ensures
            exists|j: int| 0 <= j < g && #[trigger] cuts[j + 1] - cuts[j] >= 2,
    {
        if forall|j: int| 0 <= j < g ==> #[trigger] cuts[j + 1] - cuts[j] < 2 {
            Self::lemma_cuts_sum_bound(g, cuts, g);
            assert(false);
        }
    }

    proof fn lemma_cuts_sum_bound(g: int, cuts: Seq<int>, j: int)
        requires
            g >= 1,
            cuts.len() >= g + 1,
            cuts[0] == 0,
            forall|i: int|
                #![trigger cuts[i]]
                #![trigger cuts[i + 1]]
                0 <= i < g ==> cuts[i] < cuts[i + 1],
            forall|i: int| 0 <= i < g ==> #[trigger] cuts[i + 1] - cuts[i] < 2,
            0 <= j <= g,
        ensures cuts[j as int] <= j,
        decreases j,
    {
        if j <= 0 {
        } else {
            Self::lemma_cuts_sum_bound(g, cuts, j - 1);
        }
    }

    proof fn lemma_inserted_split_valid(
        nums: Seq<i32>, g: int, cuts: Seq<int>, j: int, new_cuts: Seq<int>,
    )
        requires
            Self::is_valid_split_spec(nums.len() as int, g, cuts),
            0 <= j < g,
            cuts[j + 1] - cuts[j] >= 2,
            new_cuts == cuts.subrange(0, j + 1) + seq![cuts[j as int] + 1]
                + cuts.subrange(j + 1, cuts.len() as int),
        ensures
            Self::is_valid_split_spec(nums.len() as int, g + 1, new_cuts),
    {
        assert(new_cuts.len() == g + 2);
        assert(new_cuts[0] == cuts[0]);

        let left_mid = cuts.subrange(0, j + 1) + seq![cuts[j as int] + 1];
        let right_part = cuts.subrange(j + 1, cuts.len() as int);

        assert forall|idx: int| 0 <= idx <= j implies new_cuts[idx] == cuts[idx] by {};
        assert(new_cuts[(j + 1) as int] == cuts[j as int] + 1);
        assert forall|idx: int| j + 2 <= idx < g + 2
            implies new_cuts[idx] == cuts[(idx - 1) as int]
        by {
            assert(new_cuts[idx] == (left_mid + right_part)[idx]);
        };
        assert(new_cuts[(g + 1) as int] == cuts[g as int]);

        assert forall|i: int|
            #![trigger new_cuts[i]]
            #![trigger new_cuts[i + 1]]
            0 <= i < g + 1 implies new_cuts[i] < new_cuts[i + 1]
        by {
            if i < j {
                assert(new_cuts[i] == cuts[i]);
                assert(new_cuts[i + 1] == cuts[i + 1]);
            } else if i == j {
                assert(new_cuts[j as int] == cuts[j as int]);
                assert(new_cuts[(j + 1) as int] == cuts[j as int] + 1);
            } else if i == j + 1 {
                assert(new_cuts[(j + 1) as int] == cuts[j as int] + 1);
                assert(new_cuts[(j + 2) as int] == cuts[(j + 1) as int]);
            } else {
                assert(new_cuts[i] == cuts[(i - 1) as int]);
                assert(new_cuts[i + 1] == cuts[i as int]);
            }
        };
    }

    proof fn lemma_inserted_split_sums_bounded(
        nums: Seq<i32>, g: int, cuts: Seq<int>, j: int,
        new_cuts: Seq<int>, max_bound: int,
    )
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            Self::is_valid_split_spec(nums.len() as int, g, cuts),
            0 <= j < g,
            cuts[j + 1] - cuts[j] >= 2,
            forall|s: int|
                #![trigger cuts[s]]
                #![trigger cuts[s + 1]]
                0 <= s < g
                ==> Self::sum_range_spec(nums, cuts[s], cuts[s + 1]) <= max_bound,
            new_cuts == cuts.subrange(0, j + 1) + seq![cuts[j as int] + 1]
                + cuts.subrange(j + 1, cuts.len() as int),
        ensures
            forall|s: int|
                #![trigger new_cuts[s]]
                #![trigger new_cuts[s + 1]]
                0 <= s < g + 1
                ==> Self::sum_range_spec(nums, new_cuts[s], new_cuts[s + 1]) <= max_bound,
    {
        Self::lemma_cuts_in_range(nums.len() as int, g, cuts, j);
        Self::lemma_cuts_in_range(nums.len() as int, g, cuts, j + 1);

        let left_mid = cuts.subrange(0, j + 1) + seq![cuts[j as int] + 1];
        let right_part = cuts.subrange(j + 1, cuts.len() as int);

        assert forall|idx: int| 0 <= idx <= j implies new_cuts[idx] == cuts[idx] by {};
        assert(new_cuts[(j + 1) as int] == cuts[j as int] + 1);
        assert forall|idx: int| j + 2 <= idx < g + 2
            implies new_cuts[idx] == cuts[(idx - 1) as int]
        by {
            assert(new_cuts[idx] == (left_mid + right_part)[idx]);
        };

        
        Self::lemma_sum_range_first(nums, cuts[j as int], cuts[j + 1]);
        Self::lemma_sum_range_nonneg(nums, cuts[j as int] + 1, cuts[j + 1]);
        Self::lemma_sum_range_split(nums, cuts[j as int], cuts[j as int] + 1, cuts[j + 1]);
        Self::lemma_sum_range_nonneg(nums, cuts[j as int], cuts[j as int] + 1);

        
        assert forall|s: int|
            #![trigger new_cuts[s]]
            #![trigger new_cuts[s + 1]]
            0 <= s < g + 1
            implies Self::sum_range_spec(nums, new_cuts[s], new_cuts[s + 1]) <= max_bound
        by {
            if s < j {
                assert(new_cuts[s] == cuts[s]);
                assert(new_cuts[s + 1] == cuts[s + 1]);
                assert(Self::sum_range_spec(nums, cuts[s], cuts[s + 1]) <= max_bound);
            } else if s == j {
                assert(new_cuts[s] == cuts[j as int]);
                assert(new_cuts[s + 1] == cuts[j as int] + 1);
                assert(Self::sum_range_spec(nums, cuts[j as int], cuts[j + 1]) <= max_bound);
            } else if s == j + 1 {
                assert(new_cuts[s] == cuts[j as int] + 1);
                assert(new_cuts[s + 1] == cuts[(j + 1) as int]);
            } else {
                let t = s - 1;
                assert(new_cuts[s] == cuts[t]);
                assert(new_cuts[s + 1] == cuts[t + 1]);
                assert(0 <= t && t < g);
                assert(Self::sum_range_spec(nums, cuts[t], cuts[t + 1]) <= max_bound);
            }
        };
    }

    
    
    

    proof fn lemma_exists_valid_split(
        nums: Seq<i32>, max_sum: int, k: int,
    )
        requires
            nums.len() >= 1,
            k >= 1,
            k <= nums.len(),
            max_sum >= 0,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            max_sum >= Self::max_elem_spec(nums, nums.len() as int),
            Self::greedy_count_spec(nums, max_sum, 0, 0) <= k,
        ensures
            exists|cuts: Seq<int>|
                Self::is_valid_split_spec(nums.len() as int, k, cuts)
                && #[trigger] Self::max_segment_sum_spec(nums, k, cuts) <= max_sum,
    {
        Self::lemma_greedy_produces_valid_split(nums, max_sum);
        let g = Self::greedy_count_spec(nums, max_sum, 0, 0);
        let full_cuts = seq![0int] + Self::greedy_cuts_spec(nums, max_sum, 0, 0);
        Self::lemma_refine_split(nums, g, k, max_sum, full_cuts);
    }

    
    
    

    proof fn lemma_greedy_cs_mono(
        nums: Seq<i32>, max_sum: int, i: int, cs_lo: int, cs_hi: int,
    )
        requires
            0 <= i <= nums.len(),
            0 <= cs_lo <= cs_hi,
            forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j],
        ensures
            Self::greedy_count_spec(nums, max_sum, i, cs_lo)
                <= Self::greedy_count_spec(nums, max_sum, i, cs_hi),
            Self::greedy_count_spec(nums, max_sum, i, cs_hi)
                <= 1 + Self::greedy_count_spec(nums, max_sum, i, cs_lo),
        decreases nums.len() - i,
    {
        if i < nums.len() {
            let v = nums[i] as int;
            if cs_hi + v > max_sum && cs_lo + v > max_sum {
            } else if cs_hi + v > max_sum && cs_lo + v <= max_sum {
                Self::lemma_greedy_cs_mono(nums, max_sum, i + 1, v, cs_lo + v);
            } else {
                Self::lemma_greedy_cs_mono(nums, max_sum, i + 1, cs_lo + v, cs_hi + v);
            }
        }
    }

    proof fn lemma_greedy_maxsum_mono(
        nums: Seq<i32>, m1: int, m2: int, i: int, current_sum: int,
    )
        requires
            0 <= i <= nums.len(),
            m1 <= m2,
            current_sum >= 0,
            forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j],
        ensures
            Self::greedy_count_spec(nums, m1, i, current_sum)
                >= Self::greedy_count_spec(nums, m2, i, current_sum),
        decreases nums.len() - i,
    {
        if i < nums.len() {
            let v = nums[i] as int;
            if current_sum + v > m2 {
                Self::lemma_greedy_maxsum_mono(nums, m1, m2, i + 1, v);
            } else if current_sum + v > m1 {
                Self::lemma_greedy_maxsum_mono(nums, m1, m2, i + 1, v);
                Self::lemma_greedy_cs_mono(nums, m2, i + 1, v, current_sum + v);
            } else {
                Self::lemma_greedy_maxsum_mono(nums, m1, m2, i + 1, current_sum + v);
            }
        }
    }

    
    
    

    fn can_split(nums: &Vec<i32>, k: i32, max_sum: i64) -> (result: bool)
        requires
            nums.len() >= 1,
            nums.len() <= 1_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            k >= 1,
            0 <= max_sum <= 1_000_000_000i64,
        ensures
            result == (Self::greedy_count_spec(nums@, max_sum as int, 0, 0) <= k as int),
    {
        let mut count: i32 = 1;
        let mut current_sum: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() <= 1_000,
                1 <= count,
                count as int <= i as int + 1,
                0 <= current_sum,
                current_sum <= 1_000_000_000i64,
                0 <= max_sum <= 1_000_000_000i64,
                nums.len() >= 1,
                forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000,
                (count - 1) + Self::greedy_count_spec(
                    nums@, max_sum as int, i as int, current_sum as int,
                ) == Self::greedy_count_spec(nums@, max_sum as int, 0, 0),
            decreases nums.len() - i,
        {
            if current_sum + nums[i] as i64 > max_sum {
                count += 1;
                current_sum = nums[i] as i64;
            } else {
                current_sum += nums[i] as i64;
            }
            i += 1;
        }
        count <= k
    }

    
    
    

    pub fn split_array(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            1 <= k <= 50,
            k <= nums.len(),
        ensures
            exists|cuts: Seq<int>|
                #[trigger] Self::is_valid_split_spec(nums@.len() as int, k as int, cuts)
                && Self::max_segment_sum_spec(nums@, k as int, cuts) == result as int,
            forall|cuts: Seq<int>|
                Self::is_valid_split_spec(nums@.len() as int, k as int, cuts)
                ==> result as int <= #[trigger] Self::max_segment_sum_spec(nums@, k as int, cuts),
    {
        let n = nums.len();
        let mut left: i64 = 0;
        let mut right: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 1_000,
                forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000,
                left as int == Self::max_elem_spec(nums@, i as int),
                right as int == Self::sum_range_spec(nums@, 0, i as int),
                0 <= left <= 1_000_000i64,
                0 <= right,
                right as int <= i as int * 1_000_000,
            decreases nums.len() - i,
        {
            if nums[i] as i64 > left {
                left = nums[i] as i64;
            }
            right += nums[i] as i64;
            i += 1;
        }

        proof {
            Self::lemma_max_le_sum(nums@, nums@.len() as int);
            Self::lemma_sum_range_nonneg(nums@, 0, nums@.len() as int);
            Self::lemma_max_nonneg(nums@, nums@.len() as int);
            Self::lemma_sum_range_bounded(nums@, 0, nums@.len() as int);
            Self::lemma_greedy_no_split(nums@, right as int, 0, nums@.len() as int, 0);
        }

        let ghost left_init = left as int;

        while left < right
            invariant
                0 <= left <= right,
                right <= 1_000_000_000i64,
                1 <= nums.len() <= 1_000,
                forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000,
                1 <= k <= 50,
                k <= nums.len(),
                left as int >= left_init,
                left_init == Self::max_elem_spec(nums@, nums@.len() as int),
                Self::greedy_count_spec(nums@, right as int, 0, 0) <= k as int,
                left as int == left_init
                    || Self::greedy_count_spec(nums@, left as int - 1, 0, 0) > k as int,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            if Self::can_split(&nums, k, mid) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        proof {
            let result_val = left as int;
            let n_int = nums@.len() as int;

            assert forall|cuts: Seq<int>|
                Self::is_valid_split_spec(n_int, k as int, cuts)
                implies result_val <= #[trigger] Self::max_segment_sum_spec(nums@, k as int, cuts)
            by {
                if Self::is_valid_split_spec(n_int, k as int, cuts) {
                    let M = Self::max_segment_sum_spec(nums@, k as int, cuts);
                    assert forall|j: int|
                        #![trigger cuts[j]]
                        #![trigger cuts[j + 1]]
                        0 <= j < k as int
                        implies Self::sum_range_spec(nums@, cuts[j], cuts[j + 1]) <= M
                    by {
                        Self::lemma_max_seg_ge_each(nums@, k as int, cuts, j);
                    };
                    Self::lemma_cuts_in_range(n_int, k as int, cuts, 0);
                    Self::lemma_cuts_in_range(n_int, k as int, cuts, 1);
                    Self::lemma_sum_range_nonneg(nums@, cuts[0], cuts[1 as int]);
                    Self::lemma_max_seg_ge_each(nums@, k as int, cuts, 0);
                    Self::lemma_greedy_optimal(nums@, M, k as int, cuts);
                    if M < result_val {
                        if left as int > left_init {
                            Self::lemma_greedy_maxsum_mono(nums@, M, left as int - 1, 0, 0);
                        } else {
                            Self::lemma_max_elem_le_max_seg(nums@, k as int, cuts);
                        }
                    }
                }
            };

            Self::lemma_exists_valid_split(nums@, result_val, k as int);
            let witness: Seq<int> = choose|c: Seq<int>|
                Self::is_valid_split_spec(n_int, k as int, c)
                && #[trigger] Self::max_segment_sum_spec(nums@, k as int, c) <= result_val;
            assert(Self::max_segment_sum_spec(nums@, k as int, witness) == result_val);
        }

        left as i32
    }

    
    
    

    proof fn lemma_max_elem_le_max_seg(
        nums: Seq<i32>, k: int, cuts: Seq<int>,
    )
        requires
            Self::is_valid_split_spec(nums.len() as int, k, cuts),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            nums.len() >= 1,
        ensures
            Self::max_segment_sum_spec(nums, k, cuts)
                >= Self::max_elem_spec(nums, nums.len() as int),
    {
        Self::lemma_max_elem_in_some_segment(nums, k, cuts);
        let seg: int = choose|s: int| 0 <= s < k
            && #[trigger] Self::sum_range_spec(nums, cuts[s], cuts[s + 1])
                >= Self::max_elem_spec(nums, nums.len() as int);
        Self::lemma_max_seg_ge_each(nums, k, cuts, seg);
    }

    proof fn lemma_max_elem_in_some_segment(
        nums: Seq<i32>, k: int, cuts: Seq<int>,
    )
        requires
            Self::is_valid_split_spec(nums.len() as int, k, cuts),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            nums.len() >= 1,
        ensures
            exists|s: int| 0 <= s < k
                && #[trigger] Self::sum_range_spec(nums, cuts[s], cuts[s + 1])
                    >= Self::max_elem_spec(nums, nums.len() as int),
    {
        Self::lemma_max_elem_exists(nums, nums.len() as int);
        let idx: int = choose|idx: int| 0 <= idx < nums.len()
            && nums[idx] as int == Self::max_elem_spec(nums, nums.len() as int);
        Self::lemma_index_in_some_segment(k, cuts, nums.len() as int, idx);
        let s: int = choose|s: int| 0 <= s < k && cuts[s] <= idx && idx < #[trigger] cuts[s + 1];
        Self::lemma_cuts_in_range(nums.len() as int, k, cuts, s);
        Self::lemma_cuts_in_range(nums.len() as int, k, cuts, s + 1);
        Self::lemma_elem_le_sum_range(nums, cuts[s], cuts[s + 1], idx);
    }

    proof fn lemma_max_elem_exists(nums: Seq<i32>, end: int)
        requires
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            0 < end <= nums.len(),
        ensures
            exists|idx: int| 0 <= idx < end
                && nums[idx] as int == Self::max_elem_spec(nums, end),
        decreases end,
    {
        if end == 1 {
            assert(Self::max_elem_spec(nums, 0) == 0);
            assert(nums[0] >= 0);
        } else {
            let prev = Self::max_elem_spec(nums, end - 1);
            if nums[end - 1] as int > prev {
            } else {
                Self::lemma_max_elem_exists(nums, end - 1);
            }
        }
    }

    proof fn lemma_index_in_some_segment(
        k: int, cuts: Seq<int>, n: int, idx: int,
    )
        requires
            k >= 1,
            cuts.len() >= k + 1,
            cuts[0] == 0,
            cuts[k as int] == n,
            forall|i: int|
                #![trigger cuts[i]]
                #![trigger cuts[i + 1]]
                0 <= i < k ==> cuts[i] < cuts[i + 1],
            0 <= idx < n,
        ensures
            exists|s: int| 0 <= s < k && cuts[s] <= idx && idx < #[trigger] cuts[s + 1],
        decreases k,
    {
        if k == 1 {
        } else if idx >= cuts[(k - 1) as int] {
        } else {
            Self::lemma_index_in_some_segment(k - 1, cuts, cuts[(k - 1) as int], idx);
        }
    }

    proof fn lemma_elem_le_sum_range(
        nums: Seq<i32>, lo: int, hi: int, idx: int,
    )
        requires
            0 <= lo <= idx < hi <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
        ensures
            Self::sum_range_spec(nums, lo, hi) >= nums[idx] as int,
        decreases hi - lo,
    {
        if hi == idx + 1 {
            Self::lemma_sum_range_nonneg(nums, lo, idx);
        } else {
            Self::lemma_elem_le_sum_range(nums, lo, hi - 1, idx);
        }
    }
}
} 
