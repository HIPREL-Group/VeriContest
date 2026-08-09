use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_diag_val(nums: Seq<Vec<i32>>, i: int) -> int
        decreases nums.len() - i
    {
        if i >= nums.len() {
            0int
        } else {
            let d = i + nums[i].len() - 1;
            let rest = Self::max_diag_val(nums, i + 1);
            if d > rest { d } else { rest }
        }
    }

    pub open spec fn diag_seg(nums: Seq<Vec<i32>>, d: int, hi: int, lo: int) -> Seq<i32>
        decreases (if hi >= lo && hi >= 0 { hi - lo + 1 } else { 0 }) as nat
    {
        if hi < lo || hi < 0 {
            Seq::<i32>::empty()
        } else {
            let j = d - hi;
            let head = if hi < nums.len() && 0 <= j && j < nums[hi].len() {
                seq![nums[hi][j]]
            } else {
                Seq::<i32>::empty()
            };
            head + Self::diag_seg(nums, d, hi - 1, lo)
        }
    }

    pub open spec fn total_len(nums: Seq<Vec<i32>>, i: int) -> int
        decreases i
    {
        if i <= 0 { 0int } else { Self::total_len(nums, i - 1) + nums[i - 1].len() as int }
    }

    pub open spec fn diag_order(nums: Seq<Vec<i32>>, max_d: int) -> Seq<i32>
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat
    {
        if max_d < 0 {
            Seq::<i32>::empty()
        } else {
            let m = nums.len() as int;
            let start_i = if max_d < m { max_d } else { m - 1 };
            Self::diag_order(nums, max_d - 1) + Self::diag_seg(nums, max_d, start_i, 0)
        }
    }

    pub open spec fn diag_seg_fwd(nums: Seq<Vec<i32>>, d: int, lo: int, hi: int) -> Seq<i32>
        decreases (if hi >= lo { hi - lo + 1 } else { 0 }) as nat
    {
        if lo > hi {
            Seq::<i32>::empty()
        } else {
            let j = d - lo;
            let head = if 0 <= lo && lo < nums.len() && 0 <= j && j < nums[lo].len() {
                seq![nums[lo][j]]
            } else {
                Seq::<i32>::empty()
            };
            head + Self::diag_seg_fwd(nums, d, lo + 1, hi)
        }
    }

    proof fn lemma_diag_seg_fwd_snoc(nums: Seq<Vec<i32>>, d: int, lo: int, hi: int)
        requires
            hi >= lo,
        ensures
            Self::diag_seg_fwd(nums, d, lo, hi) == Self::diag_seg_fwd(nums, d, lo, hi - 1)
                + (if 0 <= hi && hi < nums.len() && 0 <= d - hi && d - hi < nums[hi].len() {
                    seq![nums[hi][d - hi]]
                } else {
                    Seq::<i32>::empty()
                }),
        decreases hi - lo,
    {
        if lo == hi {
            assert(Self::diag_seg_fwd(nums, d, lo + 1, hi) == Seq::<i32>::empty());
            assert(Self::diag_seg_fwd(nums, d, lo, hi - 1) == Seq::<i32>::empty());
        } else {
            Self::lemma_diag_seg_fwd_snoc(nums, d, lo + 1, hi);
            assert(Self::diag_seg_fwd(nums, d, lo, hi - 1) ==
                (if 0 <= lo && lo < nums.len() && 0 <= d - lo && d - lo < nums[lo].len() {
                    seq![nums[lo][d - lo]]
                } else {
                    Seq::<i32>::empty()
                }) + Self::diag_seg_fwd(nums, d, lo + 1, hi - 1));
        }
    }

    proof fn lemma_reverse_seg(nums: Seq<Vec<i32>>, d: int, lo: int, hi: int)
        requires
            lo >= 0,
        ensures
            Self::diag_seg(nums, d, hi, lo) == Self::diag_seg_fwd(nums, d, lo, hi).reverse(),
        decreases (if hi >= lo { hi - lo + 1 } else { 0 }) as nat,
    {
        if hi < lo {
            assert(Self::diag_seg(nums, d, hi, lo) == Seq::<i32>::empty());
            assert(Self::diag_seg_fwd(nums, d, lo, hi) == Seq::<i32>::empty());
        } else {
            Self::lemma_reverse_seg(nums, d, lo, hi - 1);
            Self::lemma_diag_seg_fwd_snoc(nums, d, lo, hi);
            let tail = if 0 <= hi && hi < nums.len() && 0 <= d - hi && d - hi < nums[hi].len() {
                seq![nums[hi][d - hi]]
            } else {
                Seq::<i32>::empty()
            };
            assert(Self::diag_seg(nums, d, hi, lo) == tail + Self::diag_seg(nums, d, hi - 1, lo));
            assert(Self::diag_seg_fwd(nums, d, lo, hi) == Self::diag_seg_fwd(nums, d, lo, hi - 1) + tail);
            assert(Self::diag_seg_fwd(nums, d, lo, hi).reverse() ==
                tail.reverse() + Self::diag_seg_fwd(nums, d, lo, hi - 1).reverse());
            assert(tail.reverse() == tail);
        }
    }

    proof fn lemma_diag_seg_fwd_trunc(nums: Seq<Vec<i32>>, d: int, hi1: int, hi2: int)
        requires
            0 <= d <= hi2 <= hi1,
        ensures
            Self::diag_seg_fwd(nums, d, 0, hi1) == Self::diag_seg_fwd(nums, d, 0, hi2),
        decreases hi1 - hi2,
    {
        if hi1 > hi2 {
            Self::lemma_diag_seg_fwd_snoc(nums, d, 0, hi1);
            Self::lemma_diag_seg_fwd_trunc(nums, d, hi1 - 1, hi2);
            assert(!(0 <= hi1 && hi1 < nums.len() && 0 <= d - hi1 && d - hi1 < nums[hi1].len()));
        }
    }

    proof fn max_diag_bound(nums: Seq<Vec<i32>>, i: int)
        requires
            0 <= i <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==>
                1 <= (#[trigger] nums[k]).len() <= 100000,
            nums.len() <= 100000,
        ensures
            Self::max_diag_val(nums, i) <= 199999,
            Self::max_diag_val(nums, i) >= 0,
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            Self::max_diag_bound(nums, i + 1);
        }
    }

    proof fn lemma_diag_seg_fwd_len_bound(nums: Seq<Vec<i32>>, d: int, hi: int)
        requires
            hi >= -1,
        ensures
            Self::diag_seg_fwd(nums, d, 0, hi).len() <= hi + 1,
        decreases (hi + 1) as nat,
    {
        if hi >= 0 {
            Self::lemma_diag_seg_fwd_snoc(nums, d, 0, hi);
            Self::lemma_diag_seg_fwd_len_bound(nums, d, hi - 1);
        } else {
            assert(Self::diag_seg_fwd(nums, d, 0, hi) =~= Seq::<i32>::empty());
        }
    }

    proof fn lemma_diag_seg_fwd_len_monotone(nums: Seq<Vec<i32>>, d: int, hi1: int, hi2: int)
        requires
            hi1 >= -1,
            hi1 <= hi2,
        ensures
            Self::diag_seg_fwd(nums, d, 0, hi1).len() <= Self::diag_seg_fwd(nums, d, 0, hi2).len(),
        decreases hi2 - hi1,
    {
        if hi1 < hi2 {
            Self::lemma_diag_seg_fwd_snoc(nums, d, 0, hi2);
            Self::lemma_diag_seg_fwd_len_monotone(nums, d, hi1, hi2 - 1);
        }
    }

    proof fn lemma_max_diag_is_upper_bound(nums: Seq<Vec<i32>>, i: int, row: int)
        requires
            0 <= i <= row < nums.len(),
        ensures
            row + nums[row].len() as int - 1 <= Self::max_diag_val(nums, i),
        decreases row - i,
    {
        if i == row {
        } else {
            Self::lemma_max_diag_is_upper_bound(nums, i + 1, row);
        }
    }

    pub open spec fn count_of(nums: Seq<Vec<i32>>, d: int) -> int {
        let m = nums.len() as int;
        let start_i = if d < m { d } else { m - 1 };
        Self::diag_seg(nums, d, start_i, 0).len() as int
    }

    pub open spec fn offset_of(nums: Seq<Vec<i32>>, d: int) -> int
        decreases (if d >= 0 { d + 1 } else { 0 }) as nat
    {
        if d <= 0 { 0 } else { Self::offset_of(nums, d - 1) + Self::count_of(nums, d - 1) }
    }

    proof fn lemma_offset_of_eq_diag_order_len(nums: Seq<Vec<i32>>, d: int)
        requires
            d >= 0,
        ensures
            Self::offset_of(nums, d) == Self::diag_order(nums, d - 1).len(),
        decreases d,
    {
        if d > 0 {
            Self::lemma_offset_of_eq_diag_order_len(nums, d - 1);
            let m = nums.len() as int;
            let start_i = if d - 1 < m { d - 1 } else { m - 1 };
            assert(Self::diag_order(nums, d - 1) == Self::diag_order(nums, d - 2) + Self::diag_seg(nums, d - 1, start_i, 0));
            assert(Self::count_of(nums, d - 1) == Self::diag_seg(nums, d - 1, start_i, 0).len() as int);
        }
    }

    proof fn lemma_count_of_eq_fwd_len(nums: Seq<Vec<i32>>, d: int)
        requires
            0 <= d,
            nums.len() >= 1,
        ensures
            Self::count_of(nums, d) == Self::diag_seg_fwd(nums, d, 0, nums.len() as int - 1).len() as int,
    {
        let m = nums.len() as int;
        let start_i = if d < m { d } else { m - 1 };
        Self::lemma_reverse_seg(nums, d, 0, start_i);
        assert(Self::diag_seg(nums, d, start_i, 0).len() == Self::diag_seg_fwd(nums, d, 0, start_i).reverse().len());
        assert(Self::diag_seg_fwd(nums, d, 0, start_i).reverse().len() == Self::diag_seg_fwd(nums, d, 0, start_i).len());
        if start_i < m - 1 {
            Self::lemma_diag_seg_fwd_trunc(nums, d, m - 1, start_i);
        }
    }

    pub open spec fn row_indicator_sum(nums: Seq<Vec<i32>>, r: int, max_d: int) -> int
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat
    {
        if max_d < 0 {
            0
        } else {
            Self::row_indicator_sum(nums, r, max_d - 1)
                + (if 0 <= r < nums.len() && 0 <= max_d - r && max_d - r < nums[r].len() { 1int } else { 0int })
        }
    }

    proof fn lemma_row_indicator_sum_below_r(nums: Seq<Vec<i32>>, r: int, md: int)
        requires
            md >= -1,
            md < r,
        ensures
            Self::row_indicator_sum(nums, r, md) == 0,
        decreases (md + 1) as nat,
    {
        if md >= 0 {
            Self::lemma_row_indicator_sum_below_r(nums, r, md - 1);
        }
    }

    proof fn lemma_row_indicator_sum_general(nums: Seq<Vec<i32>>, r: int, max_d: int)
        requires
            0 <= r < nums.len(),
            max_d >= r - 1,
        ensures
            Self::row_indicator_sum(nums, r, max_d) ==
                (if max_d - r + 1 <= nums[r].len() as int { max_d - r + 1 } else { nums[r].len() as int }),
        decreases (max_d - r + 1) as nat,
    {
        if max_d > r - 1 {
            Self::lemma_row_indicator_sum_general(nums, r, max_d - 1);
            assert(Self::row_indicator_sum(nums, r, max_d) == Self::row_indicator_sum(nums, r, max_d - 1)
                + (if 0 <= max_d - r && max_d - r < nums[r].len() { 1int } else { 0int }));
        } else {
            assert(max_d == r - 1);
            Self::lemma_row_indicator_sum_below_r(nums, r, max_d);
        }
    }

    proof fn lemma_row_indicator_sum_full(nums: Seq<Vec<i32>>, r: int, max_d: int)
        requires
            0 <= r < nums.len(),
            max_d >= r + nums[r].len() as int - 1,
        ensures
            Self::row_indicator_sum(nums, r, max_d) == nums[r].len() as int,
    {
        Self::lemma_row_indicator_sum_general(nums, r, max_d);
    }

    pub open spec fn total_diag_len_upto(nums: Seq<Vec<i32>>, max_d: int, up_to: int) -> int
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat
    {
        if max_d < 0 {
            0
        } else {
            Self::total_diag_len_upto(nums, max_d - 1, up_to)
                + Self::diag_seg_fwd(nums, max_d, 0, up_to - 1).len() as int
        }
    }

    proof fn lemma_total_diag_len_upto_zero(nums: Seq<Vec<i32>>, max_d: int)
        ensures
            Self::total_diag_len_upto(nums, max_d, 0) == 0,
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat,
    {
        if max_d >= 0 {
            Self::lemma_total_diag_len_upto_zero(nums, max_d - 1);
            assert(Self::diag_seg_fwd(nums, max_d, 0, -1).len() == 0);
        }
    }

    proof fn lemma_total_diag_len_upto_delta(nums: Seq<Vec<i32>>, max_d: int, up_to: int)
        requires
            0 <= up_to < nums.len(),
        ensures
            Self::total_diag_len_upto(nums, max_d, up_to + 1)
                == Self::total_diag_len_upto(nums, max_d, up_to) + Self::row_indicator_sum(nums, up_to, max_d),
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat,
    {
        if max_d >= 0 {
            Self::lemma_total_diag_len_upto_delta(nums, max_d - 1, up_to);
            Self::lemma_diag_seg_fwd_snoc(nums, max_d, 0, up_to);
            assert(Self::diag_seg_fwd(nums, max_d, 0, up_to).len()
                == Self::diag_seg_fwd(nums, max_d, 0, up_to - 1).len()
                    + (if 0 <= up_to && up_to < nums.len() && 0 <= max_d - up_to && max_d - up_to < nums[up_to].len() { 1int } else { 0int }));
        }
    }

    proof fn lemma_total_diag_len_upto_eq_total_len(nums: Seq<Vec<i32>>, max_d: int, up_to: int)
        requires
            0 <= up_to <= nums.len(),
            forall |r: int| 0 <= r < up_to ==> max_d >= r + (#[trigger] nums[r]).len() as int - 1,
        ensures
            Self::total_diag_len_upto(nums, max_d, up_to) == Self::total_len(nums, up_to),
        decreases up_to,
    {
        if up_to == 0 {
            Self::lemma_total_diag_len_upto_zero(nums, max_d);
        } else {
            Self::lemma_total_diag_len_upto_eq_total_len(nums, max_d, up_to - 1);
            Self::lemma_total_diag_len_upto_delta(nums, max_d, up_to - 1);
            Self::lemma_row_indicator_sum_full(nums, up_to - 1, max_d);
        }
    }

    proof fn lemma_offset_of_eq_total_diag_len_upto(nums: Seq<Vec<i32>>, max_d: int)
        requires
            nums.len() >= 1,
        ensures
            Self::offset_of(nums, max_d + 1) == Self::total_diag_len_upto(nums, max_d, nums.len() as int),
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat,
    {
        if max_d >= 0 {
            Self::lemma_offset_of_eq_total_diag_len_upto(nums, max_d - 1);
            Self::lemma_count_of_eq_fwd_len(nums, max_d);
        }
    }

    proof fn lemma_offset_of_le_total_len(nums: Seq<Vec<i32>>, d: int)
        requires
            0 <= d,
            nums.len() >= 1,
            nums.len() <= 100000,
            forall |r: int| 0 <= r < nums.len() ==> 1 <= (#[trigger] nums[r]).len() <= 100000,
            1 <= Self::total_len(nums, nums.len() as int) <= 100000,
        ensures
            0 <= Self::offset_of(nums, d) <= 100000,
    {
        let m = nums.len() as int;
        Self::max_diag_bound(nums, 0);
        let max_d = Self::max_diag_val(nums, 0);
        assert forall |r: int| 0 <= r < m implies max_d >= r + (#[trigger] nums[r]).len() as int - 1 by {
            Self::lemma_max_diag_is_upper_bound(nums, 0, r);
        }
        Self::lemma_total_diag_len_upto_eq_total_len(nums, max_d, m);
        Self::lemma_offset_of_eq_total_diag_len_upto(nums, max_d);
        assert(Self::offset_of(nums, max_d + 1) == Self::total_len(nums, m));
        Self::lemma_offset_of_nonneg(nums, d);
        if d <= max_d + 1 {
            Self::lemma_offset_of_nondecr(nums, d, max_d + 1);
        } else {
            Self::lemma_offset_of_nondecr(nums, max_d + 1, d);
            Self::lemma_offset_of_stable_above_max(nums, max_d, d);
        }
    }

    proof fn lemma_offset_of_stable_above_max(nums: Seq<Vec<i32>>, max_d: int, d: int)
        requires
            nums.len() >= 1,
            max_d >= 0,
            d > max_d + 1,
            forall |r: int| 0 <= r < nums.len() ==> max_d >= r + (#[trigger] nums[r]).len() as int - 1,
        ensures
            Self::offset_of(nums, d) == Self::offset_of(nums, max_d + 1),
        decreases d - max_d,
    {
        if d > max_d + 2 {
            Self::lemma_offset_of_stable_above_max(nums, max_d, d - 1);
            Self::lemma_count_of_zero_above_max(nums, max_d, d - 1);
        } else {
            assert(d == max_d + 2);
            Self::lemma_count_of_zero_above_max(nums, max_d, max_d + 1);
        }
    }

    proof fn lemma_count_of_zero_above_max(nums: Seq<Vec<i32>>, max_d: int, d: int)
        requires
            nums.len() >= 1,
            max_d >= 0,
            d >= max_d + 1,
            d >= 0,
            forall |r: int| 0 <= r < nums.len() ==> max_d >= r + (#[trigger] nums[r]).len() as int - 1,
        ensures
            Self::count_of(nums, d) == 0,
    {
        Self::lemma_count_of_eq_fwd_len(nums, d);
        let m = nums.len() as int;
        assert(Self::diag_seg_fwd(nums, d, 0, m - 1).len() == 0) by {
            Self::lemma_diag_seg_fwd_all_empty(nums, d, m - 1, max_d);
        }
    }

    proof fn lemma_diag_seg_fwd_all_empty(nums: Seq<Vec<i32>>, d: int, hi: int, max_d: int)
        requires
            d >= max_d + 1,
            forall |r: int| 0 <= r < nums.len() ==> max_d >= r + (#[trigger] nums[r]).len() as int - 1,
        ensures
            Self::diag_seg_fwd(nums, d, 0, hi).len() == 0,
        decreases (if hi >= 0 { hi + 1 } else { 0 }) as nat,
    {
        if hi >= 0 {
            Self::lemma_diag_seg_fwd_all_empty(nums, d, hi - 1, max_d);
            Self::lemma_diag_seg_fwd_snoc(nums, d, 0, hi);
            if 0 <= hi < nums.len() {
                assert(max_d >= hi + nums[hi].len() as int - 1);
                assert(!(0 <= d - hi && d - hi < nums[hi].len()));
            }
        } else {
            assert(Self::diag_seg_fwd(nums, d, 0, hi) =~= Seq::<i32>::empty());
        }
    }

    proof fn lemma_count_of_bound(nums: Seq<Vec<i32>>, d: int)
        requires
            0 <= d,
            nums.len() >= 1,
        ensures
            0 <= Self::count_of(nums, d) <= nums.len() as int,
    {
        let m = nums.len() as int;
        let start_i = if d < m { d } else { m - 1 };
        Self::lemma_reverse_seg(nums, d, 0, start_i);
        Self::lemma_diag_seg_fwd_len_bound(nums, d, start_i);
        assert(Self::diag_seg(nums, d, start_i, 0).len() == Self::diag_seg_fwd(nums, d, 0, start_i).reverse().len());
        assert(Self::diag_seg_fwd(nums, d, 0, start_i).reverse().len() == Self::diag_seg_fwd(nums, d, 0, start_i).len());
    }

    proof fn lemma_offset_of_bound(nums: Seq<Vec<i32>>, d: int)
        requires
            0 <= d,
            nums.len() >= 1,
        ensures
            0 <= Self::offset_of(nums, d) <= d * (nums.len() as int),
        decreases d,
    {
        if d > 0 {
            Self::lemma_offset_of_bound(nums, d - 1);
            Self::lemma_count_of_bound(nums, d - 1);
            let m = nums.len() as int;
            assert(Self::offset_of(nums, d) <= d * m) by (nonlinear_arith)
                requires
                    Self::offset_of(nums, d) == Self::offset_of(nums, d - 1) + Self::count_of(nums, d - 1),
                    Self::offset_of(nums, d - 1) <= (d - 1) * m,
                    Self::count_of(nums, d - 1) <= m;
        }
    }

    proof fn lemma_offset_of_nonneg(nums: Seq<Vec<i32>>, d: int)
        requires
            d >= 0,
            nums.len() >= 1,
        ensures
            Self::offset_of(nums, d) >= 0,
        decreases d,
    {
        if d > 0 {
            Self::lemma_offset_of_nonneg(nums, d - 1);
            Self::lemma_count_of_bound(nums, d - 1);
        }
    }

    proof fn lemma_offset_of_nondecr(nums: Seq<Vec<i32>>, d1: int, d2: int)
        requires
            0 <= d1 <= d2,
        ensures
            Self::offset_of(nums, d1) <= Self::offset_of(nums, d2),
        decreases d2 - d1,
    {
        if d1 < d2 {
            Self::lemma_offset_of_nondecr(nums, d1 + 1, d2);
            assert(Self::count_of(nums, d1) >= 0);
        }
    }

    proof fn lemma_offset_seq_mono(offset: Seq<usize>, bound: int, i: int, j: int)
        requires
            0 <= i <= j <= bound,
            bound < offset.len(),
            forall |k: int| 0 <= k < bound ==> #[trigger] offset[k] <= offset[k + 1],
        ensures
            offset[i] <= offset[j],
        decreases j - i,
    {
        if i < j {
            Self::lemma_offset_seq_mono(offset, bound, i, j - 1);
            let k = j - 1;
            assert(0 <= k < bound);
            assert(offset[k] <= offset[k + 1]);
        }
    }

    proof fn lemma_diag_order_from_result(nums: Seq<Vec<i32>>, result: Seq<i32>, offset: Seq<usize>, max_d: int)
        requires
            max_d >= -1,
            offset.len() >= max_d + 2,
            forall |dd: int| 0 <= dd <= max_d + 1 ==> (#[trigger] offset[dd]) as int == Self::offset_of(nums, dd),
            forall |dd: int| 0 <= dd <= max_d ==>
                result.subrange(#[trigger] offset[dd] as int, offset[dd + 1] as int)
                    =~= Self::diag_seg(nums, dd, (if dd < nums.len() as int { dd } else { nums.len() as int - 1 }), 0),
            result.len() == offset[max_d + 1] as int,
        ensures
            result =~= Self::diag_order(nums, max_d),
        decreases max_d + 1,
    {
        if max_d < 0 {
            assert(offset[0] as int == Self::offset_of(nums, 0));
            assert(Self::offset_of(nums, 0) == 0);
            assert(offset[0] as int == 0);
            assert(offset[max_d + 1] as int == Self::offset_of(nums, max_d + 1));
            assert(max_d + 1 == 0);
            assert(result.len() == offset[max_d + 1] as int);
            assert(result.len() == 0);
        } else {
            Self::lemma_offset_of_nondecr(nums, 0, max_d);
            let prefix = result.subrange(0, offset[max_d] as int);
            assert forall |dd: int| 0 <= dd <= max_d - 1 implies
                prefix.subrange(#[trigger] offset[dd] as int, offset[dd + 1] as int)
                    =~= Self::diag_seg(nums, dd, (if dd < nums.len() as int { dd } else { nums.len() as int - 1 }), 0) by {
                Self::lemma_offset_of_nondecr(nums, dd + 1, max_d);
                assert(prefix.subrange(offset[dd] as int, offset[dd + 1] as int)
                    =~= result.subrange(offset[dd] as int, offset[dd + 1] as int));
            }
            Self::lemma_diag_order_from_result(nums, prefix, offset, max_d - 1);
            assert(prefix =~= Self::diag_order(nums, max_d - 1));
            assert(result =~= prefix + result.subrange(offset[max_d] as int, offset[max_d + 1] as int));
            let m = nums.len() as int;
            let start_i = if max_d < m { max_d } else { m - 1 };
            assert(Self::diag_order(nums, max_d) =~= Self::diag_order(nums, max_d - 1) + Self::diag_seg(nums, max_d, start_i, 0));
        }
    }

    pub fn find_diagonal_order(nums: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums@.len() <= 100000,
            forall |i: int| 0 <= i < nums@.len() ==>
                1 <= (#[trigger] nums@[i]).len() <= 100000,
            forall |i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
                1 <= (#[trigger] nums@[i][j]) <= 100000,
            1 <= Self::total_len(nums@, nums@.len() as int) <= 100000,
        ensures
            result@ == Self::diag_order(nums@, Self::max_diag_val(nums@, 0)),
    {
        let m = nums.len();

        let mut max_d: usize = 0;
        let mut i: usize = m;
        while i > 0
            invariant
                0 <= i <= m,
                m == nums.len(),
                m <= 100000,
                forall |k: int| 0 <= k < nums@.len() ==>
                    1 <= (#[trigger] nums@[k]).len() <= 100000,
                max_d as int == Self::max_diag_val(nums@, i as int),
                max_d <= 199999,
            decreases i,
        {
            i = i - 1;
            proof {
                Self::max_diag_bound(nums@, i as int + 1);
            }
            let d = i + nums[i].len() - 1;
            if d > max_d {
                max_d = d;
            }
        }

        let mut count: Vec<usize> = Vec::new();
        let mut k: usize = 0;
        while k <= max_d
            invariant
                count.len() == k,
                k <= max_d + 1,
                max_d <= 199999,
                forall |dd: int| 0 <= dd < k ==> count@[dd] == 0,
            decreases max_d + 1 - k,
        {
            count.push(0);
            k = k + 1;
        }

        let mut i2: usize = 0;
        while i2 < m
            invariant
                count.len() == max_d + 1,
                0 <= i2 <= m,
                m == nums.len(),
                m <= 100000,
                max_d as int == Self::max_diag_val(nums@, 0),
                max_d <= 199999,
                forall |kk: int| 0 <= kk < nums@.len() ==>
                    1 <= (#[trigger] nums@[kk]).len() <= 100000,
                forall |dd: int| 0 <= dd <= max_d as int ==>
                    count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int - 1).len() as int,
            decreases m - i2,
        {
            let row_len = nums[i2].len();
            let mut j: usize = 0;
            proof {
                assert forall |dd: int| 0 <= dd <= max_d as int implies
                    (if dd < i2 as int {
                        count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int).len() as int
                    } else {
                        count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int - 1).len() as int
                    }) by {
                    if dd < i2 as int {
                        assert(!(0 <= i2 as int && (i2 as int) < nums@.len() && 0 <= dd - i2 as int && (dd - i2 as int) < nums@[i2 as int].len()));
                        Self::lemma_diag_seg_fwd_snoc(nums@, dd, 0, i2 as int);
                    }
                }
            }
            while j < row_len
                invariant
                    count.len() == max_d + 1,
                    0 <= j <= row_len,
                    row_len == nums@[i2 as int].len(),
                    i2 < m,
                    m == nums.len(),
                    m <= 100000,
                    max_d as int == Self::max_diag_val(nums@, 0),
                    max_d <= 199999,
                    forall |kk: int| 0 <= kk < nums@.len() ==>
                        1 <= (#[trigger] nums@[kk]).len() <= 100000,
                    forall |dd: int| 0 <= dd <= max_d as int ==>
                        (if dd < i2 as int + j as int {
                            count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int).len() as int
                        } else {
                            count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int - 1).len() as int
                        }),
                decreases row_len - j,
            {
                proof {
                    assert(row_len <= 100000);
                    assert(i2 < m && m <= 100000);
                    assert(i2 + j <= 200000);
                }
                let d = i2 + j;
                let ghost count_before = count@;
                proof {
                    Self::lemma_max_diag_is_upper_bound(nums@, 0, i2 as int);
                    Self::lemma_diag_seg_fwd_snoc(nums@, d as int, 0, i2 as int);
                    assert(d <= max_d);
                    Self::lemma_diag_seg_fwd_len_bound(nums@, d as int, i2 as int - 1);
                    assert(count@[d as int] as int <= i2 as int);
                    assert(count@[d as int] as int <= 100000);
                }
                count[d] = count[d] + 1;
                proof {
                    assert(count@ =~= count_before.update(d as int, (count_before[d as int] + 1) as usize));
                    assert forall |dd: int| 0 <= dd <= max_d as int implies
                        (if dd < i2 as int + (j as int + 1) {
                            count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int).len() as int
                        } else {
                            count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int - 1).len() as int
                        }) by {
                        if dd == d as int {
                            assert(Self::diag_seg_fwd(nums@, dd, 0, i2 as int) =~= Self::diag_seg_fwd(nums@, dd, 0, i2 as int - 1)
                                + (if 0 <= i2 as int && (i2 as int) < nums@.len() && 0 <= dd - i2 as int && (dd - i2 as int) < nums@[i2 as int].len() {
                                    seq![nums@[i2 as int][dd - i2 as int]]
                                } else {
                                    Seq::<i32>::empty()
                                }));
                        } else {
                            assert(count@[dd] == count_before[dd]);
                        }
                    }
                }
                j = j + 1;
            }
            proof {
                Self::lemma_max_diag_is_upper_bound(nums@, 0, i2 as int);
                assert forall |dd: int| 0 <= dd <= max_d as int implies
                    count@[dd] as int == Self::diag_seg_fwd(nums@, dd, 0, i2 as int).len() as int by {
                    if dd >= i2 as int + row_len as int {
                        assert(!(0 <= i2 as int && (i2 as int) < nums@.len() && 0 <= dd - i2 as int && (dd - i2 as int) < nums@[i2 as int].len()));
                        Self::lemma_diag_seg_fwd_snoc(nums@, dd, 0, i2 as int);
                    }
                }
            }
            i2 = i2 + 1;
        }

        proof {
            assert forall |dd: int| 0 <= dd <= max_d as int implies
                count@[dd] as int == Self::count_of(nums@, dd) by {
                Self::lemma_count_of_eq_fwd_len(nums@, dd);
            }
        }

        let mut offset: Vec<usize> = Vec::new();
        offset.push(0);
        let mut k2: usize = 0;
        while k2 <= max_d
            invariant
                offset.len() == k2 + 1,
                k2 <= max_d + 1,
                max_d <= 199999,
                m == nums.len(),
                1 <= m <= 100000,
                count.len() == max_d + 1,
                forall |kk: int| 0 <= kk < nums@.len() ==>
                    1 <= (#[trigger] nums@[kk]).len() <= 100000,
                1 <= Self::total_len(nums@, nums@.len() as int) <= 100000,
                forall |dd: int| 0 <= dd <= max_d as int ==> count@[dd] as int == Self::count_of(nums@, dd),
                forall |dd: int| 0 <= dd <= k2 as int ==> offset@[dd] as int == Self::offset_of(nums@, dd),
            decreases max_d + 1 - k2,
        {
            proof {
                Self::lemma_offset_of_le_total_len(nums@, k2 as int);
                Self::lemma_count_of_bound(nums@, k2 as int);
                assert(offset@[k2 as int] as int <= 100000);
                assert(count@[k2 as int] as int <= m as int);
                assert(count@[k2 as int] as int <= 100000);
            }
            let next = offset[k2] + count[k2];
            proof {
                assert(next as int == Self::offset_of(nums@, k2 as int) + Self::count_of(nums@, k2 as int));
                assert(next as int == Self::offset_of(nums@, k2 as int + 1));
            }
            offset.push(next);
            k2 = k2 + 1;
        }

        let total = offset[max_d + 1];

        proof {
            Self::lemma_offset_of_eq_diag_order_len(nums@, max_d as int + 1);
            assert(total as int == offset@[max_d as int + 1] as int);
            assert(total as int == Self::diag_order(nums@, max_d as int).len());
            assert forall |dd: int| 0 <= dd <= max_d as int implies offset@[dd] <= #[trigger] offset@[dd + 1] by {
                assert(offset@[dd] as int == Self::offset_of(nums@, dd));
                assert(offset@[dd + 1] as int == Self::offset_of(nums@, dd + 1));
                Self::lemma_offset_of_nondecr(nums@, dd, dd + 1);
            }
        }

        let mut result: Vec<i32> = Vec::new();
        let mut z: usize = 0;
        while z < total
            invariant
                result.len() == z,
                z <= total,
            decreases total - z,
        {
            result.push(0);
            z = z + 1;
        }

        let mut cursor: Vec<usize> = Vec::new();
        let mut k3: usize = 0;
        while k3 <= max_d
            invariant
                cursor.len() == k3,
                k3 <= max_d + 1,
                offset.len() == max_d + 2,
                forall |dd: int| 0 <= dd < k3 ==> cursor@[dd] == offset@[dd + 1],
            decreases max_d + 1 - k3,
        {
            cursor.push(offset[k3 + 1]);
            k3 = k3 + 1;
        }

        let mut i3: usize = 0;
        proof {
            assert forall |dd: int| 0 <= dd <= max_d as int implies
                result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                    =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).reverse() by {
                assert(cursor@[dd] == offset@[dd + 1]);
                Self::lemma_offset_of_nondecr(nums@, dd + 1, max_d as int + 1);
                assert(offset@[dd + 1] as int == Self::offset_of(nums@, dd + 1));
                assert(offset@[max_d as int + 1] as int == Self::offset_of(nums@, max_d as int + 1));
                assert(offset@[dd + 1] as int <= offset@[max_d as int + 1] as int);
                assert(0 <= offset@[dd + 1] as int <= result@.len());
                assert(result@.subrange(offset@[dd + 1] as int, offset@[dd + 1] as int) =~= Seq::<i32>::empty());
                assert(Self::diag_seg_fwd(nums@, dd, 0, -1) =~= Seq::<i32>::empty());
            }
        }
        while i3 < m
            invariant
                cursor.len() == max_d + 1,
                offset.len() == max_d + 2,
                result.len() == total,
                total as int == offset@[max_d as int + 1] as int,
                0 <= i3 <= m,
                m == nums.len(),
                m <= 100000,
                max_d as int == Self::max_diag_val(nums@, 0),
                max_d <= 199999,
                forall |kk: int| 0 <= kk < nums@.len() ==>
                    1 <= (#[trigger] nums@[kk]).len() <= 100000,
                forall |dd: int| 0 <= dd <= max_d as int + 1 ==> (#[trigger] offset@[dd]) as int == Self::offset_of(nums@, dd),
                forall |dd: int| 0 <= dd <= max_d as int ==>
                    offset@[dd] as int <= #[trigger] cursor@[dd] as int <= offset@[dd + 1] as int,
                forall |dd: int| 0 <= dd <= max_d as int ==>
                    (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).len() as int,
                forall |dd: int| 0 <= dd <= max_d as int ==>
                    result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                        =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).reverse(),
            decreases m - i3,
        {
            let row_len3 = nums[i3].len();
            let mut j3: usize = 0;
            proof {
                assert forall |dd: int| 0 <= dd <= max_d as int implies
                    (if dd < i3 as int {
                        (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int).len() as int
                        && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                            =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int).reverse()
                    } else {
                        (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).len() as int
                        && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                            =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).reverse()
                    }) by {
                    if dd < i3 as int {
                        assert(!(0 <= i3 as int && (i3 as int) < nums@.len() && 0 <= dd - i3 as int && (dd - i3 as int) < nums@[i3 as int].len()));
                        Self::lemma_diag_seg_fwd_snoc(nums@, dd, 0, i3 as int);
                    }
                }
            }
            while j3 < row_len3
                invariant
                    cursor.len() == max_d + 1,
                    offset.len() == max_d + 2,
                    result.len() == total,
                total as int == offset@[max_d as int + 1] as int,
                    0 <= j3 <= row_len3,
                    row_len3 == nums@[i3 as int].len(),
                    i3 < m,
                    m == nums.len(),
                    m <= 100000,
                    max_d as int == Self::max_diag_val(nums@, 0),
                    max_d <= 199999,
                    forall |kk: int| 0 <= kk < nums@.len() ==>
                        1 <= (#[trigger] nums@[kk]).len() <= 100000,
                    forall |dd: int| 0 <= dd <= max_d as int + 1 ==> (#[trigger] offset@[dd]) as int == Self::offset_of(nums@, dd),
                    forall |dd: int| 0 <= dd <= max_d as int ==>
                        offset@[dd] as int <= #[trigger] cursor@[dd] as int <= offset@[dd + 1] as int,
                    forall |dd: int| 0 <= dd <= max_d as int ==>
                        (if dd < i3 as int + j3 as int {
                            (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int).len() as int
                            && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                                =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int).reverse()
                        } else {
                            (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).len() as int
                            && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                                =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).reverse()
                        }),
                decreases row_len3 - j3,
            {
                let d = i3 + j3;
                proof {
                    Self::lemma_max_diag_is_upper_bound(nums@, 0, i3 as int);
                    Self::lemma_diag_seg_fwd_snoc(nums@, d as int, 0, i3 as int);
                    assert(Self::diag_seg_fwd(nums@, d as int, 0, i3 as int).len()
                        == Self::diag_seg_fwd(nums@, d as int, 0, i3 as int - 1).len() + 1);
                    Self::lemma_diag_seg_fwd_len_monotone(nums@, d as int, i3 as int, m as int - 1);
                    Self::lemma_count_of_eq_fwd_len(nums@, d as int);
                    assert(Self::diag_seg_fwd(nums@, d as int, 0, i3 as int).len() <= Self::count_of(nums@, d as int));
                    assert(offset@[d as int] as int == Self::offset_of(nums@, d as int));
                    assert(offset@[d as int + 1] as int == Self::offset_of(nums@, d as int + 1));
                    assert(Self::offset_of(nums@, d as int + 1) == Self::offset_of(nums@, d as int) + Self::count_of(nums@, d as int));
                    assert(Self::count_of(nums@, d as int) == offset@[d as int + 1] as int - offset@[d as int] as int);
                    assert((offset@[d as int] as int) < (cursor@[d as int] as int));
                    assert(cursor@[d as int] as int >= 1);
                    assert(cursor@[d as int] as int <= offset@[d as int + 1] as int);
                }
                let old_cursor_d = cursor[d];
                cursor[d] = cursor[d] - 1;
                proof {
                    assert((cursor@[d as int] as int) < (offset@[d as int + 1] as int));
                    Self::lemma_offset_of_nondecr(nums@, d as int + 1, max_d as int + 1);
                    assert(offset@[d as int + 1] as int == Self::offset_of(nums@, d as int + 1));
                    assert(offset@[max_d as int + 1] as int == Self::offset_of(nums@, max_d as int + 1));
                    assert(offset@[d as int + 1] as int <= offset@[max_d as int + 1] as int);
                    assert(total as int == offset@[max_d as int + 1] as int);
                    assert((cursor@[d as int] as int) < (total as int));
                }
                let val = nums[i3][j3];
                let ghost result_before = result@;
                let ghost cursor_before = cursor@;
                result.set(cursor[d], val);
                proof {
                    assert(result@ =~= result_before.update(old_cursor_d as int - 1, val));
                    assert(cursor@ =~= cursor_before.update(d as int, (old_cursor_d - 1) as usize));
                    let extra = if 0 <= i3 as int && (i3 as int) < nums@.len() && 0 <= d as int - i3 as int && (d as int - i3 as int) < nums@[i3 as int].len() {
                        seq![nums@[i3 as int][d as int - i3 as int]]
                    } else {
                        Seq::<i32>::empty()
                    };
                    assert(Self::diag_seg_fwd(nums@, d as int, 0, i3 as int) =~= Self::diag_seg_fwd(nums@, d as int, 0, i3 as int - 1) + extra);
                    assert(extra == seq![val]);
                    assert(result@.subrange(cursor@[d as int] as int, offset@[d as int + 1] as int)
                        =~= seq![val] + result_before.subrange(old_cursor_d as int, offset@[d as int + 1] as int));

                    assert forall |dd: int| 0 <= dd < d as int implies
                        (cursor@[dd] == cursor_before[dd]
                            && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                                =~= result_before.subrange(cursor@[dd] as int, offset@[dd + 1] as int)) by {
                        Self::lemma_offset_of_nondecr(nums@, dd + 1, d as int);
                        assert(offset@[dd + 1] as int == Self::offset_of(nums@, dd + 1));
                        assert(offset@[d as int] as int == Self::offset_of(nums@, d as int));
                        assert(offset@[dd + 1] as int <= offset@[d as int] as int);
                        assert(cursor@[d as int] as int >= offset@[d as int] as int);
                    }
                    assert forall |dd: int| (d as int) < dd && dd <= max_d as int implies
                        (cursor@[dd] == cursor_before[dd]
                            && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                                =~= result_before.subrange(cursor@[dd] as int, offset@[dd + 1] as int)) by {
                        Self::lemma_offset_of_nondecr(nums@, d as int + 1, dd);
                        assert(offset@[d as int + 1] as int == Self::offset_of(nums@, d as int + 1));
                        assert(offset@[dd] as int == Self::offset_of(nums@, dd));
                        assert(offset@[d as int + 1] as int <= offset@[dd] as int);
                        assert((cursor@[d as int] as int) < (offset@[d as int + 1] as int));
                        assert(offset@[dd] as int <= cursor@[dd] as int);
                        assert((cursor@[d as int] as int) < (cursor@[dd] as int));
                        assert(cursor@[dd] == cursor_before.update(d as int, (old_cursor_d - 1) as usize)[dd]);
                        Self::lemma_offset_of_nondecr(nums@, dd + 1, max_d as int + 1);
                        assert(offset@[max_d as int + 1] as int == Self::offset_of(nums@, max_d as int + 1));
                        assert(offset@[dd + 1] as int <= offset@[max_d as int + 1] as int);
                        assert(offset@[max_d as int + 1] as int == total as int);
                        assert(total as int == result@.len() as int);
                        assert(offset@[dd + 1] as int <= result@.len() as int);
                        assert((old_cursor_d as int) - 1 < result@.len() as int);
                        assert forall |kk: int| cursor@[dd] as int <= kk < offset@[dd + 1] as int implies
                            result@[kk] == result_before[kk] by {
                            assert(result@[kk] == result_before.update(old_cursor_d as int - 1, val)[kk]);
                            assert(kk != old_cursor_d as int - 1);
                        }
                        assert(result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                            =~= result_before.subrange(cursor@[dd] as int, offset@[dd + 1] as int));
                    }
                    assert forall |dd: int| 0 <= dd <= max_d as int implies
                        (if dd < i3 as int + (j3 as int + 1) {
                            (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int).len() as int
                            && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                                =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int).reverse()
                        } else {
                            (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).len() as int
                            && result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                                =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int - 1).reverse()
                        }) by {
                        if dd == d as int {
                        } else if dd < d as int {
                        } else {
                        }
                    }
                }
                j3 = j3 + 1;
            }
            proof {
                Self::lemma_max_diag_is_upper_bound(nums@, 0, i3 as int);
                assert forall |dd: int| 0 <= dd <= max_d as int implies
                    (offset@[dd + 1] as int - cursor@[dd] as int) == Self::diag_seg_fwd(nums@, dd, 0, i3 as int).len() as int by {
                    if dd >= i3 as int + row_len3 as int {
                        assert(!(0 <= i3 as int && (i3 as int) < nums@.len() && 0 <= dd - i3 as int && (dd - i3 as int) < nums@[i3 as int].len()));
                        Self::lemma_diag_seg_fwd_snoc(nums@, dd, 0, i3 as int);
                    }
                }
                assert forall |dd: int| 0 <= dd <= max_d as int implies
                    result@.subrange(cursor@[dd] as int, offset@[dd + 1] as int)
                        =~= Self::diag_seg_fwd(nums@, dd, 0, i3 as int).reverse() by {
                    if dd >= i3 as int + row_len3 as int {
                        assert(!(0 <= i3 as int && (i3 as int) < nums@.len() && 0 <= dd - i3 as int && (dd - i3 as int) < nums@[i3 as int].len()));
                        Self::lemma_diag_seg_fwd_snoc(nums@, dd, 0, i3 as int);
                    }
                }
            }
            i3 = i3 + 1;
        }

        proof {
            assert forall |dd: int| 0 <= dd <= max_d as int implies
                result@.subrange(#[trigger] offset@[dd] as int, offset@[dd + 1] as int)
                    =~= Self::diag_seg(nums@, dd, (if dd < m as int { dd } else { m as int - 1 }), 0) by {
                Self::lemma_max_diag_is_upper_bound(nums@, 0, m as int - 1);
                assert(cursor@[dd] == offset@[dd]);
                Self::lemma_reverse_seg(nums@, dd, 0, (if dd < m as int { dd } else { m as int - 1 }));
                if dd < m as int {
                    Self::lemma_diag_seg_fwd_trunc(nums@, dd, m as int - 1, dd);
                }
            }
            Self::lemma_diag_order_from_result(nums@, result@, offset@, max_d as int);
        }

        result
    }
}

}
