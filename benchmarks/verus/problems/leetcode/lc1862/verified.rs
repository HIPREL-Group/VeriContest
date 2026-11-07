use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish, lemma_mod_bound};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn inner_sum(nums: Seq<i32>, i: int, end_j: int) -> int
    decreases end_j,
{
    if end_j <= 0 {
        0
    } else {
        inner_sum(nums, i, end_j - 1) + (nums[i] as int) / (nums[end_j - 1] as int)
    }
}

pub open spec fn outer_sum(nums: Seq<i32>, end_i: int) -> int
    decreases end_i,
{
    if end_i <= 0 {
        0
    } else {
        outer_sum(nums, end_i - 1) + inner_sum(nums, end_i - 1, nums.len() as int)
    }
}

proof fn lemma_inner_sum_nonneg(nums: Seq<i32>, i: int, end_j: int)
    requires
        0 <= i < nums.len(),
        0 <= end_j <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures
        inner_sum(nums, i, end_j) >= 0,
    decreases end_j,
{
    if end_j > 0 {
        lemma_inner_sum_nonneg(nums, i, end_j - 1);
    }
}

proof fn lemma_outer_sum_nonneg(nums: Seq<i32>, end_i: int)
    requires
        0 <= end_i <= nums.len(),
        nums.len() >= 1,
        forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures
        outer_sum(nums, end_i) >= 0,
    decreases end_i,
{
    if end_i > 0 {
        lemma_outer_sum_nonneg(nums, end_i - 1);
        lemma_inner_sum_nonneg(nums, end_i - 1, nums.len() as int);
    }
}

proof fn lemma_mod_add(a: int, b: int, m: int)
    requires
        a >= 0,
        b >= 0,
        m > 0,
    ensures
        (a % m + b) % m == (a + b) % m,
{
    lemma_fundamental_div_mod(a, m);
    let q = a / m;
    assert(a % m + b == (a + b) + (-q) * m) by(nonlinear_arith)
        requires(a == m * q + a % m);
    lemma_mod_multiples_vanish(-q, a + b, m);
}








pub open spec fn count_range(nums: Seq<i32>, end: int, lo: int, hi: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        count_range(nums, end - 1, lo, hi)
            + (if lo <= nums[end - 1] && nums[end - 1] as int <= hi { 1int } else { 0int })
    }
}

proof fn count_range_step(nums: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end < nums.len(),
    ensures count_range(nums, end + 1, lo, hi)
        == count_range(nums, end, lo, hi)
            + (if lo <= nums[end] && nums[end] as int <= hi { 1int } else { 0int }),
{
}

proof fn count_range_nonneg(nums: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= nums.len(),
    ensures 0 <= count_range(nums, end, lo, hi) <= end,
    decreases end
{
    if end > 0 {
        count_range_nonneg(nums, end - 1, lo, hi);
    }
}

proof fn count_range_empty(nums: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= nums.len(), lo > hi,
    ensures count_range(nums, end, lo, hi) == 0,
    decreases end
{
    if end > 0 {
        count_range_empty(nums, end - 1, lo, hi);
    }
}

proof fn count_range_split(nums: Seq<i32>, end: int, lo: int, mid: int, hi: int)
    requires 0 <= end <= nums.len(), lo <= mid + 1, mid <= hi,
    ensures count_range(nums, end, lo, hi)
        == count_range(nums, end, lo, mid) + count_range(nums, end, mid + 1, hi),
    decreases end
{
    if end > 0 {
        count_range_split(nums, end - 1, lo, mid, hi);
        let x = nums[end - 1];
        if lo <= x && x as int <= hi {
            if x as int <= mid {
                assert(lo <= x && x as int <= mid);
                assert(!(mid + 1 <= x && x as int <= hi));
            } else {
                assert(mid + 1 <= x && x as int <= hi);
                assert(!(lo <= x && x as int <= mid));
            }
        } else {
            assert(!(lo <= x && x as int <= mid));
            assert(!(mid + 1 <= x && x as int <= hi));
        }
    }
}

proof fn count_range_cap(nums: Seq<i32>, end: int, lo: int, hi1: int, hi2: int)
    requires
        0 <= end <= nums.len(),
        hi1 <= hi2,
        forall |k: int| 0 <= k < end ==> nums[k] as int <= hi1,
    ensures count_range(nums, end, lo, hi1) == count_range(nums, end, lo, hi2),
    decreases end
{
    if end > 0 {
        count_range_cap(nums, end - 1, lo, hi1, hi2);
    }
}

pub open spec fn col_sum(nums: Seq<i32>, j: int, end_i: int) -> int
    decreases end_i
{
    if end_i <= 0 {
        0
    } else {
        col_sum(nums, j, end_i - 1) + (nums[end_i - 1] as int) / (nums[j] as int)
    }
}

pub open spec fn partial_sum(nums: Seq<i32>, ei: int, ej: int) -> int
    decreases ei
{
    if ei <= 0 {
        0
    } else {
        partial_sum(nums, ei - 1, ej) + inner_sum(nums, ei - 1, ej)
    }
}

proof fn partial_sum_eq_outer(nums: Seq<i32>, ei: int)
    requires 0 <= ei <= nums.len(),
    ensures partial_sum(nums, ei, nums.len() as int) == outer_sum(nums, ei),
    decreases ei
{
    if ei > 0 {
        partial_sum_eq_outer(nums, ei - 1);
    }
}

proof fn partial_sum_step(nums: Seq<i32>, ei: int, ej: int)
    requires 0 <= ei <= nums.len(), 0 <= ej < nums.len(),
    ensures partial_sum(nums, ei, ej + 1) == partial_sum(nums, ei, ej) + col_sum(nums, ej, ei),
    decreases ei
{
    if ei > 0 {
        partial_sum_step(nums, ei - 1, ej);
    }
}

pub open spec fn total_by_col_upto(nums: Seq<i32>, end_j: int, ei: int) -> int
    decreases end_j
{
    if end_j <= 0 {
        0
    } else {
        total_by_col_upto(nums, end_j - 1, ei) + col_sum(nums, end_j - 1, ei)
    }
}

proof fn partial_sum_zero_ej(nums: Seq<i32>, ei: int)
    requires 0 <= ei <= nums.len(),
    ensures partial_sum(nums, ei, 0) == 0,
    decreases ei
{
    if ei > 0 {
        partial_sum_zero_ej(nums, ei - 1);
    }
}

proof fn partial_sum_eq_total_by_col(nums: Seq<i32>, ei: int, ej: int)
    requires 0 <= ei <= nums.len(), 0 <= ej <= nums.len(),
    ensures partial_sum(nums, ei, ej) == total_by_col_upto(nums, ej, ei),
    decreases ej
{
    if ej <= 0 {
        partial_sum_zero_ej(nums, ei);
    } else {
        partial_sum_eq_total_by_col(nums, ei, ej - 1);
        partial_sum_step(nums, ei, ej - 1);
        assert(partial_sum(nums, ei, ej) == partial_sum(nums, ei, ej - 1) + col_sum(nums, ej - 1, ei));
        assert(total_by_col_upto(nums, ej, ei) == total_by_col_upto(nums, ej - 1, ei) + col_sum(nums, ej - 1, ei));
        assert(partial_sum(nums, ei, ej) == total_by_col_upto(nums, ej, ei));
    }
}

pub open spec fn point_indicator_sum(x: int, v: int, kmax: int) -> int
    decreases kmax
{
    if kmax <= 0 {
        0
    } else {
        point_indicator_sum(x, v, kmax - 1)
            + kmax * (if kmax * v <= x && x <= (kmax + 1) * v - 1 { 1int } else { 0int })
    }
}

proof fn floor_bucket_exists(x: int, v: int)
    requires 1 <= x, v >= 1,
    ensures (x / v) * v <= x, x <= (x / v + 1) * v - 1,
{
    lemma_fundamental_div_mod(x, v);
    lemma_mod_bound(x, v);
    assert(v * (x / v) == (x / v) * v) by (nonlinear_arith);
    assert((x / v + 1) * v == (x / v) * v + v) by (nonlinear_arith);
}

proof fn floor_bucket_unique(x: int, v: int, k: int)
    requires 1 <= x, v >= 1, k >= 0, k != x / v,
    ensures !(k * v <= x && x <= (k + 1) * v - 1),
{
    lemma_fundamental_div_mod(x, v);
    lemma_mod_bound(x, v);
    if k < x / v {
        assert((k + 1) * v <= (x / v) * v) by (nonlinear_arith)
            requires k + 1 <= x / v, v >= 1;
        assert((x / v) * v <= x);
        assert((k + 1) * v - 1 < x);
    } else {
        assert(k * v >= (x / v + 1) * v) by (nonlinear_arith)
            requires k >= x / v + 1, v >= 1;
        assert((x / v + 1) * v == (x / v) * v + v) by (nonlinear_arith);
        assert(x < (x / v) * v + v);
        assert(k * v > x);
    }
}

proof fn div_monotone(a: int, b: int, v: int)
    requires 0 <= a <= b, v >= 1,
    ensures a / v <= b / v,
{
    lemma_fundamental_div_mod(a, v);
    lemma_fundamental_div_mod(b, v);
    lemma_mod_bound(a, v);
    lemma_mod_bound(b, v);
    if a / v > b / v {
        assert((a / v) * v >= (b / v + 1) * v) by (nonlinear_arith)
            requires a / v >= b / v + 1, v >= 1;
        assert((b / v + 1) * v == (b / v) * v + v) by (nonlinear_arith);
        assert(b < (b / v) * v + v);
        assert(v * (a / v) == (a / v) * v) by (nonlinear_arith);
        assert(a >= (a / v) * v);
        assert(a > b);
    }
}

proof fn point_indicator_sum_eq(x: int, v: int, kmax: int)
    requires 1 <= x, v >= 1, kmax >= x / v, kmax >= 0,
    ensures point_indicator_sum(x, v, kmax) == x / v,
    decreases kmax
{
    if kmax <= 0 {
    } else if kmax == x / v {
        floor_bucket_exists(x, v);
        point_indicator_sum_zero(x, v, kmax - 1);
    } else {
        point_indicator_sum_eq(x, v, kmax - 1);
        floor_bucket_unique(x, v, kmax);
    }
}

proof fn point_indicator_sum_zero(x: int, v: int, kmax: int)
    requires 1 <= x, v >= 1, kmax >= 0, kmax < x / v,
    ensures point_indicator_sum(x, v, kmax) == 0,
    decreases kmax
{
    if kmax > 0 {
        point_indicator_sum_zero(x, v, kmax - 1);
        floor_bucket_unique(x, v, kmax);
    }
}

pub open spec fn g_upto_ei(nums: Seq<i32>, v: int, kmax: int, end_i: int) -> int
    decreases kmax
{
    if kmax <= 0 {
        0
    } else {
        g_upto_ei(nums, v, kmax - 1, end_i) + kmax * count_range(nums, end_i, kmax * v, (kmax + 1) * v - 1)
    }
}

proof fn g_upto_ei_step(nums: Seq<i32>, v: int, kmax: int, end_i: int)
    requires 0 <= end_i < nums.len(), v >= 1, kmax >= 0,
    ensures g_upto_ei(nums, v, kmax, end_i + 1)
        == g_upto_ei(nums, v, kmax, end_i) + point_indicator_sum(nums[end_i] as int, v, kmax),
    decreases kmax
{
    if kmax > 0 {
        g_upto_ei_step(nums, v, kmax - 1, end_i);
        count_range_step(nums, end_i, kmax * v, (kmax + 1) * v - 1);
        let x = nums[end_i] as int;
        assert(g_upto_ei(nums, v, kmax, end_i + 1)
            == g_upto_ei(nums, v, kmax - 1, end_i + 1) + kmax * count_range(nums, end_i + 1, kmax * v, (kmax + 1) * v - 1));
        assert(g_upto_ei(nums, v, kmax, end_i)
            == g_upto_ei(nums, v, kmax - 1, end_i) + kmax * count_range(nums, end_i, kmax * v, (kmax + 1) * v - 1));
        assert(count_range(nums, end_i + 1, kmax * v, (kmax + 1) * v - 1)
            == count_range(nums, end_i, kmax * v, (kmax + 1) * v - 1)
                + (if kmax * v <= x && x <= (kmax + 1) * v - 1 { 1int } else { 0int }));
        assert(point_indicator_sum(x, v, kmax)
            == point_indicator_sum(x, v, kmax - 1)
                + kmax * (if kmax * v <= x && x <= (kmax + 1) * v - 1 { 1int } else { 0int }));
        let ind = if kmax * v <= x && x <= (kmax + 1) * v - 1 { 1int } else { 0int };
        let d = count_range(nums, end_i, kmax * v, (kmax + 1) * v - 1);
        assert(kmax * (d + ind) == kmax * d + kmax * ind) by (nonlinear_arith);
        assert(g_upto_ei(nums, v, kmax, end_i + 1) == g_upto_ei(nums, v, kmax, end_i) + point_indicator_sum(x, v, kmax));
    }
}

proof fn g_upto_ei_zero(nums: Seq<i32>, v: int, kmax: int)
    requires kmax >= 0,
    ensures g_upto_ei(nums, v, kmax, 0) == 0,
    decreases kmax
{
    if kmax > 0 {
        g_upto_ei_zero(nums, v, kmax - 1);
        assert(count_range(nums, 0, kmax * v, (kmax + 1) * v - 1) == 0);
    }
}

proof fn g_upto_ei_bound(nums: Seq<i32>, v: int, kmax: int, end_i: int)
    requires 0 <= end_i <= nums.len(), v >= 1, kmax >= 0,
    ensures 0 <= g_upto_ei(nums, v, kmax, end_i) <= kmax * kmax * end_i,
    decreases kmax
{
    if kmax > 0 {
        g_upto_ei_bound(nums, v, kmax - 1, end_i);
        count_range_nonneg(nums, end_i, kmax * v, (kmax + 1) * v - 1);
        assert(kmax * count_range(nums, end_i, kmax * v, (kmax + 1) * v - 1) <= kmax * end_i) by (nonlinear_arith)
            requires 0 <= count_range(nums, end_i, kmax * v, (kmax + 1) * v - 1) <= end_i, kmax >= 0;
        assert((kmax - 1) * (kmax - 1) * end_i + kmax * end_i <= kmax * kmax * end_i) by (nonlinear_arith)
            requires kmax >= 1, end_i >= 0;
    }
}

proof fn col_sum_eq_g(nums: Seq<i32>, j: int, end_i: int, v: int, kmax: int)
    requires
        0 <= end_i <= nums.len(),
        0 <= j < nums.len(),
        v == nums[j] as int,
        v >= 1,
        kmax >= 100_000int / v,
        kmax >= 0,
        forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
    ensures col_sum(nums, j, end_i) == g_upto_ei(nums, v, kmax, end_i),
    decreases end_i
{
    if end_i <= 0 {
        g_upto_ei_zero(nums, v, kmax);
    } else {
        col_sum_eq_g(nums, j, end_i - 1, v, kmax);
        g_upto_ei_step(nums, v, kmax, end_i - 1);
        assert(1 <= nums[end_i - 1] <= 100_000);
        div_monotone(nums[end_i - 1] as int, 100_000int, v);
        point_indicator_sum_eq(nums[end_i - 1] as int, v, kmax);
        assert(col_sum(nums, j, end_i) == col_sum(nums, j, end_i - 1) + (nums[end_i - 1] as int) / v);
        assert(point_indicator_sum(nums[end_i - 1] as int, v, kmax) == (nums[end_i - 1] as int) / v);
        assert(g_upto_ei(nums, v, kmax, end_i)
            == g_upto_ei(nums, v, kmax, end_i - 1) + point_indicator_sum(nums[end_i - 1] as int, v, kmax));
        assert(col_sum(nums, j, end_i) == g_upto_ei(nums, v, kmax, end_i));
    }
}

proof fn outer_sum_eq_total_by_col(nums: Seq<i32>)
    ensures outer_sum(nums, nums.len() as int) == total_by_col_upto(nums, nums.len() as int, nums.len() as int),
{
    partial_sum_eq_outer(nums, nums.len() as int);
    partial_sum_eq_total_by_col(nums, nums.len() as int, nums.len() as int);
}

proof fn total_by_col_upto_nonneg(nums: Seq<i32>, end_j: int, ei: int)
    requires
        0 <= end_j <= nums.len(),
        0 <= ei <= nums.len(),
        forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures total_by_col_upto(nums, end_j, ei) >= 0,
    decreases end_j
{
    if end_j > 0 {
        total_by_col_upto_nonneg(nums, end_j - 1, ei);
        col_sum_nonneg(nums, end_j - 1, ei);
    }
}

proof fn col_sum_nonneg(nums: Seq<i32>, j: int, end_i: int)
    requires
        0 <= j < nums.len(),
        0 <= end_i <= nums.len(),
        forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures col_sum(nums, j, end_i) >= 0,
    decreases end_i
{
    if end_i > 0 {
        col_sum_nonneg(nums, j, end_i - 1);
    }
}

impl Solution {
    pub fn sum_of_floored_pairs(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result as int == outer_sum(nums@, nums.len() as int) % 1_000_000_007,
    {
        let n = nums.len();
        let modulo: i64 = 1_000_000_007;

        let mut count: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 100_000
            invariant
                count@.len() == vi as int,
                0 <= vi <= 100_001,
                forall |v: int| 0 <= v < vi as int ==> (#[trigger] count@[v]) as int == count_range(nums@, 0, v, v),
            decreases 100_001 - vi,
        {
            count.push(0);
            vi = vi + 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 100_000,
                count@.len() == 100_001,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums@[k] <= 100_000,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] count@[v]) as int == count_range(nums@, i as int, v, v),
                forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] count@[v] <= i as i64,
            decreases n - i,
        {
            let val = nums[i] as usize;
            proof {
                count_range_step(nums@, i as int, val as int, val as int);
                assert forall |v: int| 0 <= v <= 100_000 && v != val as int implies
                    (#[trigger] count@[v]) as int == count_range(nums@, i as int + 1, v, v) by {
                    count_range_step(nums@, i as int, v, v);
                    assert(!(v <= nums@[i as int] && nums@[i as int] as int <= v));
                }
            }
            let ghost count_before = count@;
            count.set(val, count[val] + 1);
            proof {
                assert(count@ =~= count_before.update(val as int, (count_before[val as int] + 1) as i64));
            }
            i = i + 1;
        }

        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(count[0]);
        let mut v1: usize = 1;
        while v1 <= 100_000
            invariant
                prefix@.len() == v1 as int,
                1 <= v1 <= 100_001,
                n == nums.len(),
                1 <= nums.len() <= 100_000,
                count@.len() == 100_001,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] count@[v]) as int == count_range(nums@, n as int, v, v),
                forall |v: int| 0 <= v < v1 as int ==> (#[trigger] prefix@[v]) as int == count_range(nums@, n as int, 0, v),
                forall |v: int| 0 <= v < v1 as int ==> 0 <= #[trigger] prefix@[v] <= n as i64,
            decreases 100_001 - v1,
        {
            proof {
                count_range_nonneg(nums@, n as int, 0, v1 as int);
                count_range_split(nums@, n as int, 0, v1 as int - 1, v1 as int);
                assert(prefix@[v1 as int - 1] as int + count@[v1 as int] as int <= n as int);
            }
            let next = prefix[v1 - 1] + count[v1];
            prefix.push(next);
            v1 = v1 + 1;
        }

        let mut gval: Vec<i64> = Vec::new();
        gval.push(0);
        let mut v2: usize = 1;
        while v2 <= 100_000
            invariant
                gval@.len() == v2 as int,
                1 <= v2 <= 100_001,
                n == nums.len(),
                1 <= nums.len() <= 100_000,
                prefix@.len() == 100_001,
                forall |kk: int| 0 <= kk < nums.len() ==> 1 <= #[trigger] nums@[kk] <= 100_000,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] prefix@[v]) as int == count_range(nums@, n as int, 0, v),
                forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] prefix@[v] <= n as i64,
                forall |v: int| 1 <= v < v2 as int ==> (#[trigger] gval@[v]) as int == g_upto_ei(nums@, v, 100_000int / v, n as int),
                forall |v: int| 1 <= v < v2 as int ==> 0 <= #[trigger] gval@[v] <= 2_000_000_000_000_000i64,
            decreases 100_001 - v2,
        {
            let kmax_bound: usize = 100_000 / v2;
            proof {
                lemma_fundamental_div_mod(100_000, v2 as int);
                lemma_mod_bound(100_000, v2 as int);
                assert(kmax_bound as int == 100_000int / (v2 as int));
                assert(100_000int == (v2 as int) * (kmax_bound as int) + 100_000int % (v2 as int));
                assert((kmax_bound as int) * (v2 as int) <= 100_000) by (nonlinear_arith)
                    requires 100_000int == (v2 as int) * (kmax_bound as int) + 100_000int % (v2 as int),
                        0 <= 100_000int % (v2 as int);
            }
            let mut g: i64 = 0;
            let mut k: usize = 1;
            while k <= kmax_bound
                invariant
                    1 <= v2 <= 100_000,
                    1 <= k <= kmax_bound + 1,
                    kmax_bound <= 100_000,
                    (kmax_bound as int) * (v2 as int) <= 100_000,
                    n == nums.len(),
                    1 <= nums.len() <= 100_000,
                    prefix@.len() == 100_001,
                    forall |kk: int| 0 <= kk < nums.len() ==> 1 <= #[trigger] nums@[kk] <= 100_000,
                    forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] prefix@[v]) as int == count_range(nums@, n as int, 0, v),
                    forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] prefix@[v] <= n as i64,
                    g as int == g_upto_ei(nums@, v2 as int, k as int - 1, n as int),
                    0 <= g <= 2_000_000_000_000_000i64,
                decreases kmax_bound + 1 - k,
            {
                proof {
                    assert((k as int) * (v2 as int) <= (kmax_bound as int) * (v2 as int)) by (nonlinear_arith)
                        requires k as int <= kmax_bound as int, v2 as int >= 1;
                    assert((k as int) * (v2 as int) <= 100_000);
                    assert(((k as int) + 1) * (v2 as int) <= 100_000 + v2 as int) by (nonlinear_arith)
                        requires (k as int) * (v2 as int) <= 100_000;
                }
                let lo = k * v2;
                let k1 = k + 1;
                proof {
                    assert(k1 as int == k as int + 1);
                    assert((k1 as int) * (v2 as int) <= 100_000 + v2 as int);
                    assert((k1 as int) * (v2 as int) >= 1) by (nonlinear_arith)
                        requires k1 as int >= 1, v2 as int >= 1;
                }
                let hi_raw = k1 * v2 - 1;
                let hi: usize = if hi_raw > 100_000 { 100_000 } else { hi_raw };
                proof {
                    assert(0 <= lo as int <= 100_000);
                    assert(lo as int - 1 >= 0) by (nonlinear_arith)
                        requires lo as int == k as int * v2 as int, k as int >= 1, v2 as int >= 1;
                    assert(hi_raw as int - lo as int == v2 as int - 1) by (nonlinear_arith)
                        requires hi_raw as int == (k1 as int) * (v2 as int) - 1,
                            lo as int == (k as int) * (v2 as int), k1 as int == k as int + 1;
                    assert(lo as int <= hi_raw as int) by (nonlinear_arith)
                        requires hi_raw as int - lo as int == v2 as int - 1, v2 as int >= 1;
                    assert(lo as int <= hi as int);
                    count_range_nonneg(nums@, n as int, 0, hi as int);
                    count_range_nonneg(nums@, n as int, 0, lo as int - 1);
                    count_range_split(nums@, n as int, 0, lo as int - 1, hi as int);
                    assert forall |kk: int| 0 <= kk < n as int implies 1 <= #[trigger] nums@[kk] <= 100_000 by {
                        assert(0 <= kk < nums@.len());
                    }
                    if hi_raw > 100_000 {
                        assert(hi as int == 100_000);
                        count_range_cap(nums@, n as int, lo as int, 100_000, hi_raw as int);
                    } else {
                        assert(hi as int == hi_raw as int);
                    }
                    assert(count_range(nums@, n as int, lo as int, hi as int)
                        == count_range(nums@, n as int, lo as int, hi_raw as int));
                    assert(count_range(nums@, n as int, lo as int, hi_raw as int)
                        == prefix@[hi as int] as int - prefix@[lo as int - 1] as int);
                    assert(g_upto_ei(nums@, v2 as int, k as int, n as int)
                        == g_upto_ei(nums@, v2 as int, k as int - 1, n as int)
                            + k * count_range(nums@, n as int, k as int * v2 as int, (k as int + 1) * v2 as int - 1));
                    count_range_nonneg(nums@, n as int, lo as int, hi_raw as int);
                    assert(0 <= prefix@[hi as int] as int - prefix@[lo as int - 1] as int <= n as int);
                    g_upto_ei_bound(nums@, v2 as int, k as int, n as int);
                    assert(0 <= k as int <= kmax_bound as int + 1 <= 100_001);
                    assert(0 <= n as int <= 100_000);
                    assert((k as int) * (k as int) <= 100_001 * 100_001) by (nonlinear_arith)
                        requires 0 <= k as int <= 100_001;
                    assert((k as int) * (k as int) * (n as int) <= (100_001 * 100_001) * 100_000) by (nonlinear_arith)
                        requires (k as int) * (k as int) <= 100_001 * 100_001, 0 <= (k as int) * (k as int), 0 <= n as int <= 100_000;
                    assert(g_upto_ei(nums@, v2 as int, k as int, n as int) <= 1_000_020_000_100_000);
                    assert(g as int + (k as int) * (prefix@[hi as int] as int - prefix@[lo as int - 1] as int)
                        == g_upto_ei(nums@, v2 as int, k as int, n as int));
                    assert(0 <= g as int + (k as int) * (prefix@[hi as int] as int - prefix@[lo as int - 1] as int)
                        <= 2_000_000_000_000_000);
                }
                let range_count = prefix[hi] - prefix[lo - 1];
                g = g + (k as i64) * range_count;
                k = k + 1;
            }
            proof {
                assert(k as int == kmax_bound as int + 1);
                assert(g as int == g_upto_ei(nums@, v2 as int, kmax_bound as int, n as int));
                assert(g as int == g_upto_ei(nums@, v2 as int, 100_000int / (v2 as int), n as int));
            }
            gval.push(g);
            v2 = v2 + 1;
        }

        proof {
            outer_sum_eq_total_by_col(nums@);
        }
        let mut total: i64 = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == nums.len(),
                1 <= nums.len() <= 100_000,
                modulo == 1_000_000_007,
                gval@.len() == 100_001,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums@[k] <= 100_000,
                forall |v: int| 1 <= v <= 100_000 ==> (#[trigger] gval@[v]) as int == g_upto_ei(nums@, v, 100_000int / v, n as int),
                forall |v: int| 1 <= v <= 100_000 ==> 0 <= #[trigger] gval@[v] <= 2_000_000_000_000_000i64,
                total as int == total_by_col_upto(nums@, j as int, n as int) % 1_000_000_007,
                0 <= total < 1_000_000_007,
                total_by_col_upto(nums@, j as int, n as int) >= 0,
            decreases n - j,
        {
            let val = nums[j] as usize;
            proof {
                assert(1 <= val <= 100_000);
                assert(val as int == nums@[j as int] as int);
                assert(0 <= gval@[val as int] <= 2_000_000_000_000_000i64);
                assert(0 <= total as int + gval@[val as int] as int <= 3_000_000_000_000_000);
            }
            proof {
                col_sum_eq_g(nums@, j as int, n as int, val as int, 100_000int / val as int);
                assert(gval@[val as int] as int == col_sum(nums@, j as int, n as int));
                col_sum_nonneg(nums@, j as int, n as int);
                total_by_col_upto_nonneg(nums@, j as int, n as int);
                let total_val = total_by_col_upto(nums@, j as int, n as int);
                assert(total_by_col_upto(nums@, j as int + 1, n as int) == total_val + col_sum(nums@, j as int, n as int));
                lemma_mod_add(total_val, gval@[val as int] as int, 1_000_000_007);
                assert((total_val % 1_000_000_007 + gval@[val as int] as int) % 1_000_000_007
                    == (total_val + gval@[val as int] as int) % 1_000_000_007);
                assert(total as int == total_val % 1_000_000_007);
                assert((total as int + gval@[val as int] as int) % 1_000_000_007
                    == total_by_col_upto(nums@, j as int + 1, n as int) % 1_000_000_007);
            }
            total = (total + gval[val]) % modulo;
            j = j + 1;
        }
        (total % modulo) as i32
    }
}

}
