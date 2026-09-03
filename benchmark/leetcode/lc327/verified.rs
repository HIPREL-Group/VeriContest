use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_segment_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::spec_segment_sum(nums, l, r - 1) + nums[r - 1] as int
        }
    }

    pub open spec fn spec_count_for_start(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int) -> int
        recommends
            0 <= i < nums.len(),
            i <= end_excl <= nums.len(),
        decreases end_excl - i,
    {
        if end_excl <= i {
            0
        } else {
            Self::spec_count_for_start(nums, lower, upper, i, end_excl - 1)
                + if lower <= Self::spec_segment_sum(nums, i, end_excl) <= upper {
                    1int
                } else {
                    0int
                }
        }
    }

    pub open spec fn spec_count_starts_prefix(nums: Seq<i32>, lower: int, upper: int, upto_i: int) -> int
        recommends
            0 <= upto_i <= nums.len(),
        decreases upto_i,
    {
        if upto_i <= 0 {
            0
        } else {
            Self::spec_count_starts_prefix(nums, lower, upper, upto_i - 1)
                + Self::spec_count_for_start(nums, lower, upper, upto_i - 1, nums.len() as int)
        }
    }

    pub open spec fn spec_count_range_sum(nums: Seq<i32>, lower: int, upper: int) -> int
        recommends
            1 <= nums.len(),
    {
        Self::spec_count_starts_prefix(nums, lower, upper, nums.len() as int)
    }

    proof fn lemma_count_for_start_nonneg(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int)
        requires
            0 <= i < nums.len(),
            i <= end_excl <= nums.len(),
        ensures
            0 <= Self::spec_count_for_start(nums, lower, upper, i, end_excl),
        decreases end_excl - i,
    {
        if end_excl > i {
            Self::lemma_count_for_start_nonneg(nums, lower, upper, i, end_excl - 1);
        }
    }

    proof fn lemma_count_for_start_mono(nums: Seq<i32>, lower: int, upper: int, i: int, end1: int, end2: int)
        requires
            0 <= i < nums.len(),
            i <= end1 <= end2 <= nums.len(),
        ensures
            Self::spec_count_for_start(nums, lower, upper, i, end1)
                <= Self::spec_count_for_start(nums, lower, upper, i, end2),
        decreases end2 - end1,
    {
        if end2 > end1 {
            Self::lemma_count_for_start_mono(nums, lower, upper, i, end1, end2 - 1);
            Self::lemma_count_for_start_nonneg(nums, lower, upper, i, end2);
            assert(Self::spec_count_for_start(nums, lower, upper, i, end2)
                == Self::spec_count_for_start(nums, lower, upper, i, end2 - 1)
                    + if lower <= Self::spec_segment_sum(nums, i, end2) <= upper { 1int } else { 0int });
            assert(Self::spec_count_for_start(nums, lower, upper, i, end2 - 1)
                <= Self::spec_count_for_start(nums, lower, upper, i, end2));
        }
    }

    proof fn lemma_prefix_nonneg(nums: Seq<i32>, lower: int, upper: int, upto: int)
        requires
            0 <= upto <= nums.len(),
        ensures
            0 <= Self::spec_count_starts_prefix(nums, lower, upper, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_prefix_nonneg(nums, lower, upper, upto - 1);
            Self::lemma_count_for_start_nonneg(nums, lower, upper, upto - 1, nums.len() as int);
        }
    }

    proof fn lemma_prefix_mono(nums: Seq<i32>, lower: int, upper: int, u1: int, u2: int)
        requires
            0 <= u1 <= u2 <= nums.len(),
        ensures
            Self::spec_count_starts_prefix(nums, lower, upper, u1)
                <= Self::spec_count_starts_prefix(nums, lower, upper, u2),
        decreases u2 - u1,
    {
        if u2 > u1 {
            Self::lemma_prefix_mono(nums, lower, upper, u1, u2 - 1);
            Self::lemma_count_for_start_nonneg(nums, lower, upper, u2 - 1, nums.len() as int);
            assert(Self::spec_count_starts_prefix(nums, lower, upper, u2)
                == Self::spec_count_starts_prefix(nums, lower, upper, u2 - 1)
                    + Self::spec_count_for_start(nums, lower, upper, u2 - 1, nums.len() as int));
            assert(Self::spec_count_starts_prefix(nums, lower, upper, u2 - 1)
                <= Self::spec_count_starts_prefix(nums, lower, upper, u2));
        }
    }

    proof fn lemma_prefix_bound_growing(nums: Seq<i32>, upto: int)
        requires
            0 <= upto <= nums.len(),
            forall|k: int| 0 <= k < nums.len() ==> -2147483648 <= #[trigger] nums[k] <= 2147483647,
        ensures
            -(2147483648 * upto) <= Self::spec_segment_sum(nums, 0, upto) <= 2147483647 * upto,
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_prefix_bound_growing(nums, upto - 1);
            assert(-2147483648 <= nums[upto - 1] <= 2147483647);
            assert(Self::spec_segment_sum(nums, 0, upto)
                == Self::spec_segment_sum(nums, 0, upto - 1) + nums[upto - 1] as int);
        } else {
            assert(Self::spec_segment_sum(nums, 0, upto) == 0);
        }
    }

    proof fn lemma_prefix_bound(nums: Seq<i32>, upto: int)
        requires
            0 <= upto <= nums.len(),
            nums.len() <= 100000,
            forall|k: int| 0 <= k < nums.len() ==> -2147483648 <= #[trigger] nums[k] <= 2147483647,
        ensures
            -214748364800000 <= Self::spec_segment_sum(nums, 0, upto) <= 214748364800000,
    {
        Self::lemma_prefix_bound_growing(nums, upto);
        assert(-(2147483648 * upto) >= -(2147483648 * 100000)) by (nonlinear_arith)
            requires
                0 <= upto <= 100000,
        {
        }
        assert(2147483647 * upto <= 2147483647 * 100000) by (nonlinear_arith)
            requires
                0 <= upto <= 100000,
        {
        }
    }

    proof fn lemma_segment_sum_additive(nums: Seq<i32>, i: int, mid: int, end: int)
        requires
            0 <= i <= mid <= end <= nums.len(),
        ensures
            Self::spec_segment_sum(nums, i, end) == Self::spec_segment_sum(nums, i, mid) + Self::spec_segment_sum(nums, mid, end),
        decreases end - mid,
    {
        if end > mid {
            Self::lemma_segment_sum_additive(nums, i, mid, end - 1);
        }
    }

    proof fn lemma_prefix_diff(nums: Seq<i32>, sums: Seq<i64>, i: int, end: int)
        requires
            0 <= i <= end <= nums.len(),
            sums.len() == nums.len() + 1,
            forall|k: int| 0 <= k <= nums.len() ==> sums[k] as int == Self::spec_segment_sum(nums, 0, k),
        ensures
            Self::spec_segment_sum(nums, i, end) == sums[end] as int - sums[i] as int,
    {
        Self::lemma_segment_sum_additive(nums, 0, i, end);
    }

    pub open spec fn count_matching(v: int, right: Seq<i64>, lower: int, upper: int) -> int
        decreases right.len(),
    {
        if right.len() == 0 {
            0
        } else {
            (if lower <= (right.last() as int) - v <= upper { 1int } else { 0int })
                + Self::count_matching(v, right.drop_last(), lower, upper)
        }
    }

    proof fn lemma_count_matching_concat(v: int, a: Seq<i64>, b: Seq<i64>, lower: int, upper: int)
        ensures
            Self::count_matching(v, a + b, lower, upper) == Self::count_matching(v, a, lower, upper) + Self::count_matching(v, b, lower, upper),
        decreases b.len(),
    {
        if b.len() == 0 {
            assert(a + b =~= a);
        } else {
            assert((a + b).drop_last() =~= a + b.drop_last());
            assert((a + b).last() == b.last());
            Self::lemma_count_matching_concat(v, a, b.drop_last(), lower, upper);
        }
    }

    proof fn lemma_count_matching_remove(v: int, s: Seq<i64>, k: int, lower: int, upper: int)
        requires
            0 <= k < s.len(),
        ensures
            Self::count_matching(v, s, lower, upper)
                == (if lower <= (s[k] as int) - v <= upper { 1int } else { 0int }) + Self::count_matching(v, s.remove(k), lower, upper),
        decreases s.len() - k,
    {
        if k == s.len() - 1 {
            assert(s.remove(k) =~= s.drop_last());
        } else {
            Self::lemma_count_matching_remove(v, s.drop_last(), k, lower, upper);
            assert(s.remove(k).drop_last() =~= s.drop_last().remove(k));
            assert(s.remove(k).last() == s.last());
        }
    }

    proof fn lemma_count_matching_perm(v: int, right1: Seq<i64>, right2: Seq<i64>, lower: int, upper: int)
        requires
            right1.to_multiset() =~= right2.to_multiset(),
        ensures
            Self::count_matching(v, right1, lower, upper) == Self::count_matching(v, right2, lower, upper),
        decreases right1.len(),
    {
        broadcast use vstd::seq_lib::group_to_multiset_ensures;
        assert(right1.len() == right1.to_multiset().len());
        assert(right2.len() == right2.to_multiset().len());
        if right1.len() == 0 {
            assert(right2.len() == 0);
        } else {
            let w = right1.last();
            assert(right1.contains(w));
            assert(right1.to_multiset().count(w) > 0);
            assert(right2.to_multiset().count(w) > 0);
            assert(right2.contains(w));
            let k = choose|k: int| 0 <= k < right2.len() && right2[k] == w;
            Self::lemma_count_matching_remove(v, right2, k, lower, upper);
            let right2p = right2.remove(k);
            assert(right1.drop_last() =~= right1.remove(right1.len() as int - 1));
            assert(right1.remove(right1.len() as int - 1).to_multiset() =~= right1.to_multiset().remove(right1[right1.len() as int - 1]));
            assert(right1[right1.len() as int - 1] == w);
            assert(right1.drop_last().to_multiset() =~= right1.to_multiset().remove(w));
            assert(right2p.to_multiset() =~= right2.to_multiset().remove(w));
            Self::lemma_count_matching_perm(v, right1.drop_last(), right2p, lower, upper);
        }
    }

    pub open spec fn cross_count(left: Seq<i64>, right: Seq<i64>, lower: int, upper: int) -> int
        decreases left.len(),
    {
        if left.len() == 0 {
            0
        } else {
            Self::count_matching(left[0] as int, right, lower, upper) + Self::cross_count(left.drop_first(), right, lower, upper)
        }
    }

    proof fn lemma_cross_count_remove(left: Seq<i64>, right: Seq<i64>, k: int, lower: int, upper: int)
        requires
            0 <= k < left.len(),
        ensures
            Self::cross_count(left, right, lower, upper)
                == Self::count_matching(left[k] as int, right, lower, upper) + Self::cross_count(left.remove(k), right, lower, upper),
        decreases k,
    {
        if k == 0 {
            assert(left.remove(0) =~= left.drop_first());
        } else {
            Self::lemma_cross_count_remove(left.drop_first(), right, k - 1, lower, upper);
            assert(left.remove(k).drop_first() =~= left.drop_first().remove(k - 1));
            assert(left.remove(k)[0] == left[0]);
            assert(left.drop_first()[k - 1] == left[k]);
        }
    }

    proof fn lemma_cross_count_left_perm(left1: Seq<i64>, left2: Seq<i64>, right: Seq<i64>, lower: int, upper: int)
        requires
            left1.to_multiset() =~= left2.to_multiset(),
        ensures
            Self::cross_count(left1, right, lower, upper) == Self::cross_count(left2, right, lower, upper),
        decreases left1.len(),
    {
        broadcast use vstd::seq_lib::group_to_multiset_ensures;
        assert(left1.len() == left1.to_multiset().len());
        assert(left2.len() == left2.to_multiset().len());
        if left1.len() == 0 {
            assert(left2.len() == 0);
        } else {
            let v = left1[0];
            assert(left1.contains(v));
            assert(left1.to_multiset().count(v) > 0);
            assert(left2.to_multiset().count(v) > 0);
            assert(left2.contains(v));
            let k = choose|k: int| 0 <= k < left2.len() && left2[k] == v;
            Self::lemma_cross_count_remove(left2, right, k, lower, upper);
            let left2p = left2.remove(k);
            assert(left1.drop_first() =~= left1.remove(0));
            assert(left1.remove(0).to_multiset() =~= left1.to_multiset().remove(left1[0]));
            assert(left1.drop_first().to_multiset() =~= left1.to_multiset().remove(v));
            assert(left2p.to_multiset() =~= left2.to_multiset().remove(v));
            Self::lemma_cross_count_left_perm(left1.drop_first(), left2p, right, lower, upper);
        }
    }

    proof fn lemma_cross_count_right_perm(left: Seq<i64>, right1: Seq<i64>, right2: Seq<i64>, lower: int, upper: int)
        requires
            right1.to_multiset() =~= right2.to_multiset(),
        ensures
            Self::cross_count(left, right1, lower, upper) == Self::cross_count(left, right2, lower, upper),
        decreases left.len(),
    {
        if left.len() > 0 {
            Self::lemma_count_matching_perm(left[0] as int, right1, right2, lower, upper);
            Self::lemma_cross_count_right_perm(left.drop_first(), right1, right2, lower, upper);
        }
    }

    proof fn lemma_cross_count_left_concat(a: Seq<i64>, b: Seq<i64>, right: Seq<i64>, lower: int, upper: int)
        ensures
            Self::cross_count(a + b, right, lower, upper) == Self::cross_count(a, right, lower, upper) + Self::cross_count(b, right, lower, upper),
        decreases a.len(),
    {
        if a.len() == 0 {
            assert(a + b =~= b);
        } else {
            assert((a + b).drop_first() =~= a.drop_first() + b);
            assert((a + b)[0] == a[0]);
            Self::lemma_cross_count_left_concat(a.drop_first(), b, right, lower, upper);
        }
    }

    proof fn lemma_cross_count_right_concat(left: Seq<i64>, a: Seq<i64>, b: Seq<i64>, lower: int, upper: int)
        ensures
            Self::cross_count(left, a + b, lower, upper) == Self::cross_count(left, a, lower, upper) + Self::cross_count(left, b, lower, upper),
        decreases left.len(),
    {
        if left.len() > 0 {
            Self::lemma_count_matching_concat(left[0] as int, a, b, lower, upper);
            Self::lemma_cross_count_right_concat(left.drop_first(), a, b, lower, upper);
        }
    }

    proof fn lemma_cross_count_singleton(w: i64, right: Seq<i64>, lower: int, upper: int)
        ensures
            Self::cross_count(seq![w], right, lower, upper) == Self::count_matching(w as int, right, lower, upper),
    {
        assert(seq![w].len() == 1);
        assert(seq![w][0] == w);
        assert(seq![w].drop_first() =~= Seq::<i64>::empty());
        assert(Self::cross_count(Seq::<i64>::empty(), right, lower, upper) == 0);
        assert(Self::cross_count(seq![w], right, lower, upper)
            == Self::count_matching(seq![w][0] as int, right, lower, upper) + Self::cross_count(seq![w].drop_first(), right, lower, upper));
    }

    pub open spec fn count_pairs_range(sums: Seq<i64>, l: int, r: int, lower: int, upper: int) -> int
        decreases r - l,
    {
        if r - l <= 1 {
            0
        } else {
            Self::count_matching(sums[l] as int, sums.subrange(l + 1, r), lower, upper)
                + Self::count_pairs_range(sums, l + 1, r, lower, upper)
        }
    }

    proof fn lemma_count_pairs_range_additive(sums: Seq<i64>, l: int, mid: int, r: int, lower: int, upper: int)
        requires
            0 <= l <= mid <= r <= sums.len(),
        ensures
            Self::count_pairs_range(sums, l, r, lower, upper)
                == Self::count_pairs_range(sums, l, mid, lower, upper)
                    + Self::count_pairs_range(sums, mid, r, lower, upper)
                    + Self::cross_count(sums.subrange(l, mid), sums.subrange(mid, r), lower, upper),
        decreases mid - l,
    {
        if mid == l {
            assert(sums.subrange(l, mid) =~= Seq::<i64>::empty());
        } else {
            Self::lemma_count_pairs_range_additive(sums, l + 1, mid, r, lower, upper);
            assert(sums.subrange(l + 1, r) =~= sums.subrange(l + 1, mid) + sums.subrange(mid, r));
            Self::lemma_count_matching_concat(sums[l] as int, sums.subrange(l + 1, mid), sums.subrange(mid, r), lower, upper);
            assert(sums.subrange(l, mid) =~= seq![sums[l]] + sums.subrange(l + 1, mid));
            Self::lemma_cross_count_left_concat(seq![sums[l]], sums.subrange(l + 1, mid), sums.subrange(mid, r), lower, upper);
            Self::lemma_cross_count_singleton(sums[l], sums.subrange(mid, r), lower, upper);
        }
    }

    pub open spec fn range_pair_count(sums: Seq<i64>, l: int, r: int, lower: int, upper: int) -> int
        decreases r - l,
    {
        if r - l <= 1 {
            0
        } else {
            let mid = l + (r - l) / 2;
            Self::range_pair_count(sums, l, mid, lower, upper)
                + Self::range_pair_count(sums, mid, r, lower, upper)
                + Self::cross_count(sums.subrange(l, mid), sums.subrange(mid, r), lower, upper)
        }
    }

    proof fn lemma_range_pair_count_eq_top_split(sums: Seq<i64>, l: int, mid: int, r: int, lower: int, upper: int)
        requires
            0 <= l <= mid <= r <= sums.len(),
            mid == l + (r - l) / 2,
            r - l > 1,
        ensures
            Self::range_pair_count(sums, l, r, lower, upper)
                == Self::range_pair_count(sums, l, mid, lower, upper)
                    + Self::range_pair_count(sums, mid, r, lower, upper)
                    + Self::cross_count(sums.subrange(l, mid), sums.subrange(mid, r), lower, upper),
    {
    }

    proof fn lemma_range_pair_count_subrange_eq(sums1: Seq<i64>, sums2: Seq<i64>, l: int, r: int, lower: int, upper: int)
        requires
            0 <= l <= r <= sums1.len(),
            0 <= l <= r <= sums2.len(),
            sums1.subrange(l, r) =~= sums2.subrange(l, r),
        ensures
            Self::range_pair_count(sums1, l, r, lower, upper) == Self::range_pair_count(sums2, l, r, lower, upper),
        decreases r - l,
    {
        if r - l > 1 {
            let mid = l + (r - l) / 2;
            assert(sums1.subrange(l, mid) =~= sums1.subrange(l, r).subrange(0, mid - l));
            assert(sums2.subrange(l, mid) =~= sums2.subrange(l, r).subrange(0, mid - l));
            assert(sums1.subrange(mid, r) =~= sums1.subrange(l, r).subrange(mid - l, r - l));
            assert(sums2.subrange(mid, r) =~= sums2.subrange(l, r).subrange(mid - l, r - l));
            Self::lemma_range_pair_count_subrange_eq(sums1, sums2, l, mid, lower, upper);
            Self::lemma_range_pair_count_subrange_eq(sums1, sums2, mid, r, lower, upper);
        }
    }

    proof fn lemma_range_pair_count_eq(sums: Seq<i64>, l: int, r: int, lower: int, upper: int)
        requires
            0 <= l <= r <= sums.len(),
        ensures
            Self::range_pair_count(sums, l, r, lower, upper) == Self::count_pairs_range(sums, l, r, lower, upper),
        decreases r - l,
    {
        if r - l > 1 {
            let mid = l + (r - l) / 2;
            Self::lemma_range_pair_count_eq(sums, l, mid, lower, upper);
            Self::lemma_range_pair_count_eq(sums, mid, r, lower, upper);
            Self::lemma_count_pairs_range_additive(sums, l, mid, r, lower, upper);
        }
    }

    proof fn lemma_count_matching_eq_count_for_start(nums: Seq<i32>, sums: Seq<i64>, lower: int, upper: int, i: int, end_excl: int)
        requires
            0 <= i,
            i <= end_excl <= nums.len(),
            sums.len() == nums.len() + 1,
            forall|k: int| 0 <= k <= nums.len() ==> sums[k] as int == Self::spec_segment_sum(nums, 0, k),
        ensures
            Self::count_matching(sums[i] as int, sums.subrange(i + 1, end_excl + 1), lower, upper)
                == Self::spec_count_for_start(nums, lower, upper, i, end_excl),
        decreases end_excl - i,
    {
        if end_excl <= i {
            assert(sums.subrange(i + 1, end_excl + 1) =~= Seq::<i64>::empty());
        } else {
            Self::lemma_count_matching_eq_count_for_start(nums, sums, lower, upper, i, end_excl - 1);
            assert(sums.subrange(i + 1, end_excl + 1).drop_last() =~= sums.subrange(i + 1, end_excl));
            assert(sums.subrange(i + 1, end_excl + 1).last() == sums[end_excl]);
            Self::lemma_prefix_diff(nums, sums, i, end_excl);
        }
    }

    proof fn lemma_count_pairs_range_eq_prefix(nums: Seq<i32>, sums: Seq<i64>, lower: int, upper: int, upto_i: int)
        requires
            0 <= upto_i <= nums.len(),
            sums.len() == nums.len() + 1,
            forall|k: int| 0 <= k <= nums.len() ==> sums[k] as int == Self::spec_segment_sum(nums, 0, k),
        ensures
            Self::count_pairs_range(sums, 0, upto_i, lower, upper)
                + Self::cross_count(sums.subrange(0, upto_i), sums.subrange(upto_i, nums.len() as int + 1), lower, upper)
                == Self::spec_count_starts_prefix(nums, lower, upper, upto_i),
        decreases upto_i,
    {
        let n = nums.len() as int;
        if upto_i > 0 {
            Self::lemma_count_pairs_range_eq_prefix(nums, sums, lower, upper, upto_i - 1);
            Self::lemma_count_pairs_range_additive(sums, 0, upto_i - 1, upto_i, lower, upper);
            assert(sums.subrange(upto_i - 1, upto_i) =~= seq![sums[upto_i - 1]]);
            assert(sums.subrange(0, upto_i) =~= sums.subrange(0, upto_i - 1) + seq![sums[upto_i - 1]]);
            Self::lemma_cross_count_left_concat(sums.subrange(0, upto_i - 1), seq![sums[upto_i - 1]], sums.subrange(upto_i, n + 1), lower, upper);
            Self::lemma_cross_count_singleton(sums[upto_i - 1], sums.subrange(upto_i, n + 1), lower, upper);
            assert(sums.subrange(upto_i - 1, n + 1) =~= seq![sums[upto_i - 1]] + sums.subrange(upto_i, n + 1));
            Self::lemma_cross_count_right_concat(sums.subrange(0, upto_i - 1), seq![sums[upto_i - 1]], sums.subrange(upto_i, n + 1), lower, upper);
            Self::lemma_cross_count_singleton(sums[upto_i - 1], sums.subrange(upto_i, n + 1), lower, upper);
            Self::lemma_count_matching_eq_count_for_start(nums, sums, lower, upper, upto_i - 1, n);
        }
    }

    proof fn lemma_range_pair_count_top(nums: Seq<i32>, sums: Seq<i64>, lower: int, upper: int)
        requires
            1 <= nums.len(),
            sums.len() == nums.len() + 1,
            forall|k: int| 0 <= k <= nums.len() ==> sums[k] as int == Self::spec_segment_sum(nums, 0, k),
        ensures
            Self::range_pair_count(sums, 0, nums.len() as int + 1, lower, upper)
                == Self::spec_count_range_sum(nums, lower, upper),
    {
        let n = nums.len() as int;
        Self::lemma_range_pair_count_eq(sums, 0, n + 1, lower, upper);
        Self::lemma_count_pairs_range_eq_prefix(nums, sums, lower, upper, n);
        Self::lemma_count_pairs_range_additive(sums, 0, n, n + 1, lower, upper);
        assert(Self::count_pairs_range(sums, n, n + 1, lower, upper) == 0);
        assert(Self::count_pairs_range(sums, 0, n + 1, lower, upper)
            == Self::count_pairs_range(sums, 0, n, lower, upper)
                + Self::cross_count(sums.subrange(0, n), sums.subrange(n, n + 1), lower, upper));
        assert(Self::count_pairs_range(sums, 0, n, lower, upper)
            + Self::cross_count(sums.subrange(0, n), sums.subrange(n, n + 1), lower, upper)
            == Self::spec_count_starts_prefix(nums, lower, upper, n));
        assert(Self::spec_count_starts_prefix(nums, lower, upper, n) == Self::spec_count_range_sum(nums, lower, upper));
    }

    proof fn lemma_count_matching_bound(v: int, right: Seq<i64>, lower: int, upper: int)
        ensures
            0 <= Self::count_matching(v, right, lower, upper) <= right.len(),
        decreases right.len(),
    {
        if right.len() > 0 {
            Self::lemma_count_matching_bound(v, right.drop_last(), lower, upper);
        }
    }

    proof fn lemma_cross_count_bound(left: Seq<i64>, right: Seq<i64>, lower: int, upper: int)
        ensures
            0 <= Self::cross_count(left, right, lower, upper) <= left.len() * right.len(),
        decreases left.len(),
    {
        if left.len() > 0 {
            Self::lemma_count_matching_bound(left[0] as int, right, lower, upper);
            Self::lemma_cross_count_bound(left.drop_first(), right, lower, upper);
            assert(left.len() * right.len() == (left.len() - 1) * right.len() + right.len()) by (nonlinear_arith);
        }
    }

    proof fn lemma_range_pair_count_bound(sums: Seq<i64>, l: int, r: int, lower: int, upper: int)
        requires
            0 <= l <= r <= sums.len(),
        ensures
            0 <= Self::range_pair_count(sums, l, r, lower, upper) <= (r - l) * (r - l),
        decreases r - l,
    {
        if r - l > 1 {
            let mid = l + (r - l) / 2;
            Self::lemma_range_pair_count_bound(sums, l, mid, lower, upper);
            Self::lemma_range_pair_count_bound(sums, mid, r, lower, upper);
            Self::lemma_cross_count_bound(sums.subrange(l, mid), sums.subrange(mid, r), lower, upper);
            assert(sums.subrange(l, mid).len() == mid - l);
            assert(sums.subrange(mid, r).len() == r - mid);
            assert(mid - l >= 0 && r - mid >= 0);
            assert((mid - l) * (mid - l) + (r - mid) * (r - mid) + (mid - l) * (r - mid) <= (r - l) * (r - l)) by (nonlinear_arith)
                requires
                    mid - l >= 0,
                    r - mid >= 0,
            {
            }
        }
    }

    pub open spec fn sorted_range(sums: Seq<i64>, l: int, r: int) -> bool {
        forall|i: int, j: int| l <= i <= j < r ==> sums[i] <= sums[j]
    }

    proof fn lemma_count_matching_zero(v: int, right: Seq<i64>, lower: int, upper: int)
        requires
            forall|p: int| 0 <= p < right.len() ==> !(lower <= (#[trigger] right[p] as int) - v <= upper),
        ensures
            Self::count_matching(v, right, lower, upper) == 0,
        decreases right.len(),
    {
        if right.len() > 0 {
            Self::lemma_count_matching_zero(v, right.drop_last(), lower, upper);
        }
    }

    proof fn lemma_two_pointer_count(right: Seq<i64>, v: int, lo: int, hi: int, lower: int, upper: int)
        requires
            Self::sorted_range(right, 0, right.len() as int),
            0 <= lo <= right.len(),
            0 <= hi <= right.len(),
            lo <= hi,
            forall|p: int| 0 <= p < lo ==> (right[p] as int) - v < lower,
            lo == right.len() as int || (right[lo] as int) - v >= lower,
            forall|p: int| 0 <= p < hi ==> (right[p] as int) - v <= upper,
            hi == right.len() as int || (right[hi] as int) - v > upper,
        ensures
            (hi - lo) as int == Self::count_matching(v, right, lower, upper),
        decreases right.len(),
    {
        if right.len() > 0 {
            let m = right.len() as int - 1;
            if hi == right.len() as int {
                if lo == hi {
                    assert forall|p: int| 0 <= p < right.len() implies !(lower <= (#[trigger] right[p] as int) - v <= upper) by {
                        assert(p < lo);
                    }
                    Self::lemma_count_matching_zero(v, right, lower, upper);
                } else {
                    assert(right[m] as int - v <= upper);
                    assert(lo != right.len() as int);
                    assert(right[lo] as int - v >= lower);
                    assert(right[m] as int >= right[lo] as int);
                    Self::lemma_two_pointer_count(right.drop_last(), v, lo, m, lower, upper);
                }
            } else {
                assert(hi <= m);
                assert(right[hi] as int - v > upper);
                assert(right[m] as int >= right[hi] as int);
                Self::lemma_two_pointer_count(right.drop_last(), v, lo, hi, lower, upper);
            }
        }
    }

    fn sort_count(sums: &mut Vec<i64>, buf: &mut Vec<i64>, l: usize, r: usize, lower: i64, upper: i64) -> (count: i64)
        requires
            l <= r <= old(sums).len(),
            old(sums).len() <= 100001,
            old(buf).len() == old(sums).len(),
            -100000 <= lower <= upper <= 100000,
            forall|k: int| 0 <= k < old(sums).len() ==> -214748364800000 <= #[trigger] old(sums)[k] <= 214748364800000,
        ensures
            sums.len() == old(sums).len(),
            buf.len() == old(sums).len(),
            forall|k: int| (0 <= k < l as int || r as int <= k < sums.len() as int) ==> sums[k] == old(sums)[k],
            forall|k: int| 0 <= k < old(sums).len() ==> -214748364800000 <= #[trigger] sums[k] <= 214748364800000,
            Self::sorted_range(sums@, l as int, r as int),
            sums@.subrange(l as int, r as int).to_multiset() =~= old(sums)@.subrange(l as int, r as int).to_multiset(),
            count as int == Self::range_pair_count(old(sums)@, l as int, r as int, lower as int, upper as int),
            0 <= count as int <= (r as int - l as int) * (r as int - l as int),
        decreases r - l,
    {
        if r - l <= 1 {
            proof {
                assert((r as int - l as int) * (r as int - l as int) >= 0) by (nonlinear_arith);
            }
            return 0;
        }

        let mid = l + (r - l) / 2;
        let ghost sums_at_entry = sums@;
        let count1 = Self::sort_count(sums, buf, l, mid, lower, upper);
        let ghost sums_after_left = sums@;
        let count2 = Self::sort_count(sums, buf, mid, r, lower, upper);
        let ghost sums_after_right = sums@;

        assert(forall|k: int| mid as int <= k < r as int ==> sums_after_left[k] == sums_at_entry[k]);
        assert(sums@.subrange(l as int, mid as int) =~= sums_after_left.subrange(l as int, mid as int));
        assert(sums@.subrange(mid as int, r as int).to_multiset() =~= sums_after_left.subrange(mid as int, r as int).to_multiset());
        assert(sums_after_left.subrange(mid as int, r as int) =~= sums_at_entry.subrange(mid as int, r as int));

        proof {
            Self::lemma_range_pair_count_subrange_eq(sums_after_left, sums_at_entry, mid as int, r as int, lower as int, upper as int);
        }

        proof {
            assert(mid as int - l as int <= 100001);
            assert(r as int - mid as int <= 100001);
            assert((mid as int - l as int) * (mid as int - l as int) <= 100001 * 100001) by (nonlinear_arith)
                requires
                    mid as int - l as int <= 100001,
                    mid as int - l as int >= 0,
            {
            }
            assert((r as int - mid as int) * (r as int - mid as int) <= 100001 * 100001) by (nonlinear_arith)
                requires
                    r as int - mid as int <= 100001,
                    r as int - mid as int >= 0,
            {
            }
        }
        let mut count = count1 + count2;

        let mut lo: usize = mid;
        let mut hi: usize = mid;
        let mut i: usize = l;
        let ghost sums_sorted = sums@;
        while i < mid
            invariant
                sums@ == sums_sorted,
                l <= i <= mid, mid <= lo <= r, mid <= hi <= r, lo <= hi,
                mid <= r <= sums_sorted.len(),
                sums_sorted.len() <= 100001,
                -100000 <= lower <= upper <= 100000,
                i == l ==> (lo == mid && hi == mid),
                forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                Self::sorted_range(sums_sorted, l as int, mid as int),
                Self::sorted_range(sums_sorted, mid as int, r as int),
                i > l ==> forall|p: int| mid as int <= p < lo as int ==> (#[trigger] sums_sorted[p] as int) - (sums_sorted[i as int - 1] as int) < lower as int,
                i > l ==> (lo as int == r as int || (sums_sorted[lo as int] as int) - (sums_sorted[i as int - 1] as int) >= lower as int),
                i > l ==> forall|p: int| mid as int <= p < hi as int ==> (#[trigger] sums_sorted[p] as int) - (sums_sorted[i as int - 1] as int) <= upper as int,
                i > l ==> (hi as int == r as int || (sums_sorted[hi as int] as int) - (sums_sorted[i as int - 1] as int) > upper as int),
                count as int == count1 as int + count2 as int
                    + Self::cross_count(sums_sorted.subrange(l as int, i as int), sums_sorted.subrange(mid as int, r as int), lower as int, upper as int),
                0 <= count1 as int <= (mid as int - l as int) * (mid as int - l as int),
                0 <= count2 as int <= (r as int - mid as int) * (r as int - mid as int),
            decreases mid - i,
        {
            let ghost lo0 = lo;
            proof {
                if i > l {
                    assert forall|p: int| mid as int <= p < lo0 as int implies (#[trigger] sums_sorted[p] as int) - (sums_sorted[i as int] as int) < lower as int by {
                        assert((sums_sorted[p] as int) - (sums_sorted[i as int - 1] as int) < lower as int);
                        assert(sums_sorted[i as int] as int >= sums_sorted[i as int - 1] as int);
                    }
                } else {
                    assert(lo0 as int == mid as int);
                }
            }
            while lo < r && sums[lo] - sums[i] < lower
                invariant
                    sums@ == sums_sorted,
                    mid <= lo <= r, l <= i < mid,
                    mid <= r <= sums_sorted.len(),
                    forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                    forall|p: int| mid as int <= p < lo as int ==> (#[trigger] sums_sorted[p] as int) - (sums_sorted[i as int] as int) < lower as int,
                decreases r - lo,
            {
                lo += 1;
            }
            let ghost hi0 = hi;
            proof {
                if i > l {
                    assert forall|p: int| mid as int <= p < hi0 as int implies (#[trigger] sums_sorted[p] as int) - (sums_sorted[i as int] as int) <= upper as int by {
                        assert((sums_sorted[p] as int) - (sums_sorted[i as int - 1] as int) <= upper as int);
                        assert(sums_sorted[i as int] as int >= sums_sorted[i as int - 1] as int);
                    }
                } else {
                    assert(hi0 as int == mid as int);
                }
            }
            while hi < r && sums[hi] - sums[i] <= upper
                invariant
                    sums@ == sums_sorted,
                    mid <= hi <= r, l <= i < mid,
                    mid <= r <= sums_sorted.len(),
                    forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                    forall|p: int| mid as int <= p < hi as int ==> (#[trigger] sums_sorted[p] as int) - (sums_sorted[i as int] as int) <= upper as int,
                decreases r - hi,
            {
                hi += 1;
            }
            proof {
                assert(lo <= r);
                assert(hi <= r);
                assert(lo <= hi) by {
                    if lo > hi {
                        assert(hi < lo);
                        assert((sums_sorted[hi as int] as int) - (sums_sorted[i as int] as int) < lower as int);
                        if hi < r {
                            assert((sums_sorted[hi as int] as int) - (sums_sorted[i as int] as int) > upper as int);
                            assert(false);
                        } else {
                            assert(hi == r);
                            assert(lo <= r);
                            assert(false);
                        }
                    }
                }
                Self::lemma_two_pointer_count(
                    sums_sorted.subrange(mid as int, r as int),
                    sums_sorted[i as int] as int,
                    lo as int - mid as int,
                    hi as int - mid as int,
                    lower as int,
                    upper as int,
                );
                assert((hi as int - mid as int) - (lo as int - mid as int)
                    == Self::count_matching(sums_sorted[i as int] as int, sums_sorted.subrange(mid as int, r as int), lower as int, upper as int));
                assert((hi - lo) as int == hi as int - lo as int);
            }
            proof {
                Self::lemma_cross_count_bound(
                    sums_sorted.subrange(l as int, i as int),
                    sums_sorted.subrange(mid as int, r as int),
                    lower as int,
                    upper as int,
                );
                assert(sums_sorted.subrange(l as int, i as int).len() == i as int - l as int);
                assert(sums_sorted.subrange(mid as int, r as int).len() == r as int - mid as int);
                assert((i as int - l as int) * (r as int - mid as int) <= 100001 * 100001) by (nonlinear_arith)
                    requires
                        i as int - l as int <= 100001,
                        i as int - l as int >= 0,
                        r as int - mid as int <= 100001,
                        r as int - mid as int >= 0,
                {
                }
                assert((mid as int - l as int) * (mid as int - l as int) <= 100001 * 100001) by (nonlinear_arith)
                    requires
                        mid as int - l as int <= 100001,
                        mid as int - l as int >= 0,
                {
                }
                assert((r as int - mid as int) * (r as int - mid as int) <= 100001 * 100001) by (nonlinear_arith)
                    requires
                        r as int - mid as int <= 100001,
                        r as int - mid as int >= 0,
                {
                }
            }
            count = count + ((hi - lo) as i64);
            proof {
                assert(sums_sorted.subrange(l as int, i as int + 1) =~= sums_sorted.subrange(l as int, i as int) + seq![sums_sorted[i as int]]);
                Self::lemma_cross_count_left_concat(
                    sums_sorted.subrange(l as int, i as int),
                    seq![sums_sorted[i as int]],
                    sums_sorted.subrange(mid as int, r as int),
                    lower as int,
                    upper as int,
                );
                Self::lemma_cross_count_singleton(sums_sorted[i as int], sums_sorted.subrange(mid as int, r as int), lower as int, upper as int);
            }
            i += 1;
        }

        proof {
            assert(sums_sorted.subrange(l as int, mid as int) =~= sums_sorted.subrange(l as int, i as int));
            assert(count as int == count1 as int + count2 as int
                + Self::cross_count(sums_sorted.subrange(l as int, mid as int), sums_sorted.subrange(mid as int, r as int), lower as int, upper as int));
            Self::lemma_range_pair_count_eq_top_split(sums_at_entry, l as int, mid as int, r as int, lower as int, upper as int);
            assert(Self::range_pair_count(sums_at_entry, l as int, r as int, lower as int, upper as int)
                == count1 as int + count2 as int
                    + Self::cross_count(sums_at_entry.subrange(l as int, mid as int), sums_at_entry.subrange(mid as int, r as int), lower as int, upper as int));
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            assert(sums_sorted.subrange(l as int, mid as int).to_multiset() =~= sums_at_entry.subrange(l as int, mid as int).to_multiset());
            assert(sums_sorted.subrange(mid as int, r as int).to_multiset() =~= sums_at_entry.subrange(mid as int, r as int).to_multiset());
            Self::lemma_cross_count_left_perm(
                sums_sorted.subrange(l as int, mid as int),
                sums_at_entry.subrange(l as int, mid as int),
                sums_sorted.subrange(mid as int, r as int),
                lower as int,
                upper as int,
            );
            Self::lemma_cross_count_right_perm(
                sums_at_entry.subrange(l as int, mid as int),
                sums_sorted.subrange(mid as int, r as int),
                sums_at_entry.subrange(mid as int, r as int),
                lower as int,
                upper as int,
            );
            Self::lemma_range_pair_count_bound(sums_at_entry, l as int, r as int, lower as int, upper as int);
        }

        let mut i2: usize = l;
        let mut j2: usize = mid;
        let mut k2: usize = l;
        while i2 < mid && j2 < r
            invariant
                sums@ == sums_sorted,
                buf.len() == sums_sorted.len(),
                mid <= r <= sums_sorted.len(),
                l <= i2 <= mid, mid <= j2 <= r, k2 == i2 + (j2 - mid), l <= k2 <= r,
                forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                Self::sorted_range(sums_sorted, l as int, mid as int),
                Self::sorted_range(sums_sorted, mid as int, r as int),
                Self::sorted_range(buf@, l as int, k2 as int),
                buf@.subrange(l as int, k2 as int).to_multiset()
                    =~= sums_sorted.subrange(l as int, i2 as int).to_multiset().add(sums_sorted.subrange(mid as int, j2 as int).to_multiset()),
                i2 < mid ==> (k2 == l || forall|p: int| l as int <= p < k2 as int ==> buf@[p] <= sums_sorted[i2 as int]),
                j2 < r ==> (k2 == l || forall|p: int| l as int <= p < k2 as int ==> buf@[p] <= sums_sorted[j2 as int]),
            decreases (mid - i2) + (r - j2),
        {
            let ghost old_buf = buf@;
            if sums[i2] <= sums[j2] {
                buf[k2] = sums[i2];
                proof {
                    assert(buf@.subrange(l as int, k2 as int + 1) =~= old_buf.subrange(l as int, k2 as int).push(sums_sorted[i2 as int]));
                    assert(sums_sorted.subrange(l as int, i2 as int + 1) =~= sums_sorted.subrange(l as int, i2 as int).push(sums_sorted[i2 as int]));
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                }
                i2 += 1;
            } else {
                buf[k2] = sums[j2];
                proof {
                    assert(buf@.subrange(l as int, k2 as int + 1) =~= old_buf.subrange(l as int, k2 as int).push(sums_sorted[j2 as int]));
                    assert(sums_sorted.subrange(mid as int, j2 as int + 1) =~= sums_sorted.subrange(mid as int, j2 as int).push(sums_sorted[j2 as int]));
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                }
                j2 += 1;
            }
            k2 += 1;
        }
        while i2 < mid
            invariant
                sums@ == sums_sorted,
                buf.len() == sums_sorted.len(),
                mid <= r <= sums_sorted.len(),
                forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                l <= i2 <= mid, mid <= j2 <= r, k2 == i2 + (j2 - mid), l <= k2 <= r,
                i2 < mid ==> j2 == r,
                Self::sorted_range(sums_sorted, l as int, mid as int),
                Self::sorted_range(buf@, l as int, k2 as int),
                buf@.subrange(l as int, k2 as int).to_multiset()
                    =~= sums_sorted.subrange(l as int, i2 as int).to_multiset().add(sums_sorted.subrange(mid as int, j2 as int).to_multiset()),
                i2 < mid ==> (k2 == l || forall|p: int| l as int <= p < k2 as int ==> buf@[p] <= sums_sorted[i2 as int]),
                j2 < r ==> (k2 == l || forall|p: int| l as int <= p < k2 as int ==> buf@[p] <= sums_sorted[j2 as int]),
            decreases mid - i2,
        {
            let ghost old_buf = buf@;
            buf[k2] = sums[i2];
            proof {
                assert(buf@.subrange(l as int, k2 as int + 1) =~= old_buf.subrange(l as int, k2 as int).push(sums_sorted[i2 as int]));
                assert(sums_sorted.subrange(l as int, i2 as int + 1) =~= sums_sorted.subrange(l as int, i2 as int).push(sums_sorted[i2 as int]));
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
            }
            i2 += 1;
            k2 += 1;
        }
        while j2 < r
            invariant
                sums@ == sums_sorted,
                buf.len() == sums_sorted.len(),
                mid <= r <= sums_sorted.len(),
                forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                i2 == mid, mid <= j2 <= r, k2 == i2 + (j2 - mid), l <= k2 <= r,
                Self::sorted_range(sums_sorted, mid as int, r as int),
                Self::sorted_range(buf@, l as int, k2 as int),
                buf@.subrange(l as int, k2 as int).to_multiset()
                    =~= sums_sorted.subrange(l as int, i2 as int).to_multiset().add(sums_sorted.subrange(mid as int, j2 as int).to_multiset()),
                j2 < r ==> (k2 == l || forall|p: int| l as int <= p < k2 as int ==> buf@[p] <= sums_sorted[j2 as int]),
            decreases r - j2,
        {
            let ghost old_buf = buf@;
            buf[k2] = sums[j2];
            proof {
                assert(buf@.subrange(l as int, k2 as int + 1) =~= old_buf.subrange(l as int, k2 as int).push(sums_sorted[j2 as int]));
                assert(sums_sorted.subrange(mid as int, j2 as int + 1) =~= sums_sorted.subrange(mid as int, j2 as int).push(sums_sorted[j2 as int]));
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
            }
            j2 += 1;
            k2 += 1;
        }

        assert(i2 == mid && j2 == r && k2 == r);
        assert(sums_sorted.subrange(l as int, mid as int).to_multiset().add(sums_sorted.subrange(mid as int, r as int).to_multiset())
            =~= sums_sorted.subrange(l as int, r as int).to_multiset()) by {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            vstd::seq_lib::lemma_multiset_commutative(sums_sorted.subrange(l as int, mid as int), sums_sorted.subrange(mid as int, r as int));
            assert(sums_sorted.subrange(l as int, mid as int) + sums_sorted.subrange(mid as int, r as int) =~= sums_sorted.subrange(l as int, r as int));
        }
        assert(sums_at_entry.subrange(l as int, mid as int).to_multiset().add(sums_at_entry.subrange(mid as int, r as int).to_multiset())
            =~= sums_at_entry.subrange(l as int, r as int).to_multiset()) by {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            vstd::seq_lib::lemma_multiset_commutative(sums_at_entry.subrange(l as int, mid as int), sums_at_entry.subrange(mid as int, r as int));
            assert(sums_at_entry.subrange(l as int, mid as int) + sums_at_entry.subrange(mid as int, r as int) =~= sums_at_entry.subrange(l as int, r as int));
        }
        assert(sums_sorted.subrange(l as int, r as int).to_multiset() =~= sums_at_entry.subrange(l as int, r as int).to_multiset());

        let mut idx2: usize = l;
        while idx2 < r
            invariant
                buf.len() == sums.len(),
                sums.len() == sums_sorted.len(),
                r <= sums_sorted.len(),
                forall|k: int| 0 <= k < sums_sorted.len() ==> -214748364800000 <= #[trigger] sums_sorted[k] <= 214748364800000,
                l <= idx2 <= r,
                forall|k: int| (0 <= k < l as int || r as int <= k < sums.len() as int) ==> sums[k] == sums_sorted[k],
                forall|k: int| l as int <= k < idx2 as int ==> sums[k] == buf[k],
                forall|k: int| idx2 as int <= k < r as int ==> sums[k] == sums_sorted[k],
            decreases r - idx2,
        {
            sums[idx2] = buf[idx2];
            idx2 += 1;
        }

        proof {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            assert(sums@.subrange(l as int, r as int) =~= buf@.subrange(l as int, r as int));
            assert(Self::sorted_range(sums@, l as int, r as int));
            assert(sums@.subrange(l as int, r as int).to_multiset() =~= sums_sorted.subrange(l as int, r as int).to_multiset());
            assert(sums_sorted.subrange(l as int, r as int).to_multiset() =~= sums_at_entry.subrange(l as int, r as int).to_multiset());
            assert(forall|k: int| (0 <= k < l as int || r as int <= k < sums@.len() as int) ==> sums[k] == sums_at_entry[k]);
            assert forall|k: int| 0 <= k < sums_at_entry.len() implies -214748364800000 <= #[trigger] sums@[k] <= 214748364800000 by {
                if l as int <= k < r as int {
                    assert(sums@[k] == buf@[k]);
                    assert(sums@.subrange(l as int, r as int)[k - l as int] == sums@[k]);
                    assert(sums@.subrange(l as int, r as int).contains(sums@[k]));
                    assert(sums_sorted.subrange(l as int, r as int).to_multiset().count(sums@[k]) > 0);
                    assert(sums_sorted.subrange(l as int, r as int).contains(sums@[k]));
                    let p = choose|p: int| 0 <= p < sums_sorted.subrange(l as int, r as int).len()
                        && sums_sorted.subrange(l as int, r as int)[p] == sums@[k];
                    assert(sums_sorted[l as int + p] == sums@[k]);
                    assert(0 <= l as int + p < sums_sorted.len());
                    assert(-214748364800000 <= sums_sorted[l as int + p] <= 214748364800000);
                } else {
                    assert(sums@[k] == sums_at_entry[k]);
                    assert(-214748364800000 <= sums_at_entry[k] <= 214748364800000);
                }
            }
        }

        count
    }

    pub fn count_range_sum(nums: Vec<i32>, lower: i32, upper: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100000,
            forall|i: int| 0 <= i < nums.len() ==> -2147483648 <= #[trigger] nums[i] <= 2147483647,
            -100000 <= lower as int <= upper as int <= 100000,
            Self::spec_count_range_sum(nums@, lower as int, upper as int) <= i32::MAX,
        ensures
            res as int == Self::spec_count_range_sum(nums@, lower as int, upper as int),
    {
        let n = nums.len();
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        let mut t: usize = 0;
        while t < n + 1
            invariant
                n == nums.len(),
                n <= 100000,
                t <= n + 1,
                prefix.len() == t,
                forall|k: int| 0 <= k < t as int ==> prefix[k] == 0,
            decreases n + 1 - t,
        {
            prefix.push(0i64);
            t += 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                n <= 100000,
                prefix.len() == n + 1,
                0 <= i <= n,
                forall|k: int| 0 <= k <= i as int ==> prefix[k] as int == Self::spec_segment_sum(nums@, 0, k),
                forall|k: int| (i as int) < k <= n as int ==> prefix[k] == 0,
                forall|k: int| 0 <= k < nums.len() ==> -2147483648 <= #[trigger] nums@[k] <= 2147483647,
            decreases n - i,
        {
            proof {
                assert(-2147483648 <= nums@[i as int] <= 2147483647);
                assert(prefix[i as int] as int == Self::spec_segment_sum(nums@, 0, i as int));
                Self::lemma_prefix_bound(nums@, i as int);
            }
            let v = prefix[i] + nums[i] as i64;
            proof {
                assert(-100000 * 2147483648i64 <= prefix[i as int] as i64 <= 100000 * 2147483648i64) by (nonlinear_arith)
                    requires
                        prefix[i as int] as int == Self::spec_segment_sum(nums@, 0, i as int),
                        -214748364800000 <= Self::spec_segment_sum(nums@, 0, i as int) <= 214748364800000,
                {
                }
            }
            prefix[i + 1] = v;
            proof {
                assert(Self::spec_segment_sum(nums@, 0, i as int + 1)
                    == Self::spec_segment_sum(nums@, 0, i as int) + nums@[i as int] as int);
            }
            i += 1;
        }

        let mut buf: Vec<i64> = Vec::with_capacity(n + 1);
        let mut t2: usize = 0;
        while t2 < n + 1
            invariant
                n == nums.len(),
                n <= 100000,
                t2 <= n + 1,
                buf.len() == t2,
            decreases n + 1 - t2,
        {
            buf.push(0i64);
            t2 += 1;
        }

        proof {
            assert(forall|k: int| 0 <= k <= n as int ==> prefix@[k] as int == Self::spec_segment_sum(nums@, 0, k));
            assert forall|k: int| 0 <= k < prefix@.len() implies -214748364800000 <= #[trigger] prefix@[k] <= 214748364800000 by {
                Self::lemma_prefix_bound(nums@, k);
            }
        }

        let ghost prefix_before = prefix@;
        let res_i64 = Self::sort_count(&mut prefix, &mut buf, 0, n + 1, lower as i64, upper as i64);

        proof {
            assert(res_i64 as int == Self::range_pair_count(prefix_before, 0, n as int + 1, lower as int, upper as int));
            Self::lemma_range_pair_count_top(nums@, prefix_before, lower as int, upper as int);
            assert(res_i64 as int == Self::spec_count_range_sum(nums@, lower as int, upper as int));
            Self::lemma_prefix_nonneg(nums@, lower as int, upper as int, n as int);
            assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int)
                == Self::spec_count_range_sum(nums@, lower as int, upper as int));
            assert(0 <= res_i64 as int <= i32::MAX);
        }

        res_i64 as i32
    }
}

}
