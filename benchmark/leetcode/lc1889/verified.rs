use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_concat_contains_all_elements;

fn main() {}

verus! {

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn count_le(s: Seq<int>, v: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] <= v {
        1 + count_le(s.drop_first(), v)
    } else {
        count_le(s.drop_first(), v)
    }
}

pub open spec fn merge_seq(a: Seq<int>, b: Seq<int>) -> Seq<int>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]] + merge_seq(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq(a, b.drop_first())
    }
}

pub open spec fn all_ge(s: Seq<int>, lo: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= lo
}

proof fn lemma_count_le_cons(x: int, rest: Seq<int>, v: int)
    ensures count_le(seq![x] + rest, v) == (if x <= v { 1int } else { 0int }) + count_le(rest, v),
{
    assert((seq![x] + rest).drop_first() =~= rest);
    assert((seq![x] + rest)[0] == x);
}

proof fn lemma_merge_seq_len(a: Seq<int>, b: Seq<int>)
    ensures merge_seq(a, b).len() == a.len() + b.len(),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_len(a.drop_first(), b);
    } else {
        lemma_merge_seq_len(a, b.drop_first());
    }
}

proof fn lemma_merge_seq_count_le(a: Seq<int>, b: Seq<int>, v: int)
    ensures count_le(merge_seq(a, b), v) == count_le(a, v) + count_le(b, v),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_count_le(a.drop_first(), b, v);
        lemma_count_le_cons(a[0], merge_seq(a.drop_first(), b), v);
        lemma_count_le_cons(a[0], a.drop_first(), v);
    } else {
        lemma_merge_seq_count_le(a, b.drop_first(), v);
        lemma_count_le_cons(b[0], merge_seq(a, b.drop_first()), v);
        lemma_count_le_cons(b[0], b.drop_first(), v);
    }
}

proof fn lemma_merge_seq_all_ge(a: Seq<int>, b: Seq<int>, lo: int)
    requires all_ge(a, lo), all_ge(b, lo),
    ensures all_ge(merge_seq(a, b), lo),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_all_ge(a.drop_first(), b, lo);
    } else {
        lemma_merge_seq_all_ge(a, b.drop_first(), lo);
    }
}

proof fn lemma_sorted_drop_first(s: Seq<int>)
    requires sorted_asc(s), s.len() > 0,
    ensures sorted_asc(s.drop_first()), all_ge(s.drop_first(), s[0]),
{
    assert forall|i: int, j: int| 0 <= i <= j < s.drop_first().len() implies
        s.drop_first()[i] <= s.drop_first()[j] by {
        assert(s.drop_first()[i] == s[i + 1]);
        assert(s.drop_first()[j] == s[j + 1]);
    }
    assert forall|i: int| 0 <= i < s.drop_first().len() implies s.drop_first()[i] >= s[0] by {
        assert(s.drop_first()[i] == s[i + 1]);
    }
}

proof fn lemma_sorted_cons(x: int, rest: Seq<int>)
    requires all_ge(rest, x), sorted_asc(rest),
    ensures sorted_asc(seq![x] + rest),
{
    assert forall|i: int, j: int| 0 <= i <= j < (seq![x] + rest).len() implies
        (seq![x] + rest)[i] <= (seq![x] + rest)[j] by {
        if i == 0 {
            if j > 0 {
                assert((seq![x] + rest)[j] == rest[j - 1]);
                assert(rest[j - 1] >= x);
            }
        } else {
            assert((seq![x] + rest)[i] == rest[i - 1]);
            assert((seq![x] + rest)[j] == rest[j - 1]);
        }
    }
}

proof fn lemma_merge_seq_sorted(a: Seq<int>, b: Seq<int>)
    requires sorted_asc(a), sorted_asc(b),
    ensures sorted_asc(merge_seq(a, b)),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_sorted_drop_first(a);
        lemma_merge_seq_sorted(a.drop_first(), b);
        lemma_merge_seq_all_ge(a.drop_first(), b, a[0]);
        lemma_sorted_cons(a[0], merge_seq(a.drop_first(), b));
    } else {
        lemma_sorted_drop_first(b);
        lemma_merge_seq_sorted(a, b.drop_first());
        lemma_merge_seq_all_ge(a, b.drop_first(), b[0]);
        lemma_sorted_cons(b[0], merge_seq(a, b.drop_first()));
    }
}

proof fn lemma_count_le_split(s: Seq<int>, mid: int, v: int)
    requires 0 <= mid <= s.len(),
    ensures count_le(s, v) == count_le(s.subrange(0, mid), v) + count_le(s.subrange(mid, s.len() as int), v),
    decreases mid
{
    if mid == 0 {
        assert(s.subrange(0, 0) =~= Seq::<int>::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(s.len() > 0);
        lemma_count_le_split(s.drop_first(), mid - 1, v);
        assert(s.drop_first().subrange(0, mid - 1) =~= s.subrange(1, mid));
        assert(s.drop_first().subrange(mid - 1, s.drop_first().len() as int) =~= s.subrange(mid, s.len() as int));
        assert(s.subrange(0, mid) =~= seq![s[0]] + s.subrange(1, mid));
        lemma_count_le_cons(s[0], s.subrange(1, mid), v);
    }
}

pub open spec fn merge_sort_seq(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let mid = s.len() as int / 2;
        merge_seq(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)))
    }
}

proof fn lemma_merge_sort_seq_sorted(s: Seq<int>)
    ensures sorted_asc(merge_sort_seq(s)),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_sorted(s.subrange(0, mid));
        lemma_merge_sort_seq_sorted(s.subrange(mid, s.len() as int));
        lemma_merge_seq_sorted(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
    }
}

proof fn lemma_merge_sort_seq_count_le(s: Seq<int>, v: int)
    ensures count_le(merge_sort_seq(s), v) == count_le(s, v),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_count_le(s.subrange(0, mid), v);
        lemma_merge_sort_seq_count_le(s.subrange(mid, s.len() as int), v);
        lemma_merge_seq_count_le(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), v);
        lemma_count_le_split(s, mid, v);
    }
}

proof fn lemma_merge_sort_seq_len(s: Seq<int>)
    ensures merge_sort_seq(s).len() == s.len(),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_len(s.subrange(0, mid));
        lemma_merge_sort_seq_len(s.subrange(mid, s.len() as int));
        lemma_merge_seq_len(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
    }
}

pub open spec fn pkg_count_range(packages: Seq<i32>, end: int, lo: int, hi: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        pkg_count_range(packages, end - 1, lo, hi)
            + (if lo <= packages[end - 1] && packages[end - 1] as int <= hi { 1int } else { 0int })
    }
}

pub open spec fn pkg_sum_range(packages: Seq<i32>, end: int, lo: int, hi: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        pkg_sum_range(packages, end - 1, lo, hi)
            + (if lo <= packages[end - 1] && packages[end - 1] as int <= hi { packages[end - 1] as int } else { 0int })
    }
}

proof fn lemma_pkg_count_range_step(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end < packages.len(),
    ensures pkg_count_range(packages, end + 1, lo, hi)
        == pkg_count_range(packages, end, lo, hi)
            + (if lo <= packages[end] && packages[end] as int <= hi { 1int } else { 0int }),
{
}

proof fn lemma_pkg_sum_range_step(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end < packages.len(),
    ensures pkg_sum_range(packages, end + 1, lo, hi)
        == pkg_sum_range(packages, end, lo, hi)
            + (if lo <= packages[end] && packages[end] as int <= hi { packages[end] as int } else { 0int }),
{
}

proof fn lemma_pkg_count_range_nonneg(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= packages.len(),
    ensures 0 <= pkg_count_range(packages, end, lo, hi) <= end,
    decreases end
{
    if end > 0 {
        lemma_pkg_count_range_nonneg(packages, end - 1, lo, hi);
    }
}

proof fn lemma_pkg_sum_range_bound(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= packages.len(), hi >= 0,
        forall |k: int| 0 <= k < end ==> 0 <= #[trigger] packages[k] as int <= hi,
    ensures 0 <= pkg_sum_range(packages, end, lo, hi) <= hi * end,
    decreases end
{
    if end > 0 {
        lemma_pkg_sum_range_bound(packages, end - 1, lo, hi);
        assert(hi * (end - 1) + hi == hi * end) by (nonlinear_arith);
    }
}

proof fn lemma_pkg_count_range_split(packages: Seq<i32>, end: int, lo: int, mid: int, hi: int)
    requires 0 <= end <= packages.len(), lo <= mid + 1, mid <= hi,
    ensures pkg_count_range(packages, end, lo, hi)
        == pkg_count_range(packages, end, lo, mid) + pkg_count_range(packages, end, mid + 1, hi),
    decreases end
{
    if end > 0 {
        lemma_pkg_count_range_split(packages, end - 1, lo, mid, hi);
        let x = packages[end - 1];
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

proof fn lemma_pkg_sum_range_split(packages: Seq<i32>, end: int, lo: int, mid: int, hi: int)
    requires 0 <= end <= packages.len(), lo <= mid + 1, mid <= hi,
    ensures pkg_sum_range(packages, end, lo, hi)
        == pkg_sum_range(packages, end, lo, mid) + pkg_sum_range(packages, end, mid + 1, hi),
    decreases end
{
    if end > 0 {
        lemma_pkg_sum_range_split(packages, end - 1, lo, mid, hi);
        let x = packages[end - 1];
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

proof fn lemma_pkg_count_range_empty(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= packages.len(), lo > hi,
    ensures pkg_count_range(packages, end, lo, hi) == 0,
    decreases end
{
    if end > 0 {
        lemma_pkg_count_range_empty(packages, end - 1, lo, hi);
    }
}

proof fn lemma_pkg_sum_range_empty(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= packages.len(), lo > hi,
    ensures pkg_sum_range(packages, end, lo, hi) == 0,
    decreases end
{
    if end > 0 {
        lemma_pkg_sum_range_empty(packages, end - 1, lo, hi);
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn min_box_upto(boxes_j: Seq<i32>, pkg: i32, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::min_box_upto(boxes_j, pkg, end - 1);
            let cur = boxes_j[end - 1] as int;
            if cur >= pkg as int {
                if prev == -1 || cur <= prev { cur } else { prev }
            } else {
                prev
            }
        }
    }

    pub open spec fn can_fit_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> bool
        decreases end
    {
        if end <= 0 {
            true
        } else {
            Self::can_fit_upto(packages, boxes_j, end - 1)
                && Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) >= packages[end - 1] as int
        }
    }

    pub open spec fn waste_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            (Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) - packages[end - 1] as int)
                + Self::waste_upto(packages, boxes_j, end - 1)
        }
    }

    pub open spec fn total_boxes_len(boxes: Seq<Vec<i32>>, j: int) -> int
        decreases j
    {
        if j <= 0 { 0int } else { Self::total_boxes_len(boxes, j - 1) + boxes[j - 1]@.len() as int }
    }

    pub open spec fn best_waste_upto(packages: Seq<i32>, boxes: Seq<Vec<i32>>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::best_waste_upto(packages, boxes, end - 1);
            let boxes_j = boxes[end - 1]@;
            let n = packages.len() as int;
            if Self::can_fit_upto(packages, boxes_j, n) {
                let w = Self::waste_upto(packages, boxes_j, n);
                if prev == -1 || w < prev { w } else { prev }
            } else {
                prev
            }
        }
    }
}

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map_values(|x: i32| x as int)
}

pub open spec fn min_box_int(s: Seq<int>, pkg: int, end: int) -> int
    decreases end
{
    if end <= 0 {
        -1
    } else {
        let prev = min_box_int(s, pkg, end - 1);
        let cur = s[end - 1];
        if cur >= pkg {
            if prev == -1 || cur <= prev { cur } else { prev }
        } else {
            prev
        }
    }
}

proof fn lemma_min_box_int_eq_min_box_upto(boxes_j: Seq<i32>, pkg: i32, end: int)
    requires 0 <= end <= boxes_j.len(),
    ensures min_box_int(to_int_seq(boxes_j), pkg as int, end) == Solution::min_box_upto(boxes_j, pkg, end),
    decreases end
{
    if end > 0 {
        lemma_min_box_int_eq_min_box_upto(boxes_j, pkg, end - 1);
        assert(to_int_seq(boxes_j)[end - 1] == boxes_j[end - 1] as int);
    }
}

proof fn lemma_min_box_int_witness(s: Seq<int>, pkg: int, end: int)
    requires
        0 <= end <= s.len(),
        forall |k: int| 0 <= k < s.len() ==> #[trigger] s[k] >= 0,
    ensures
        min_box_int(s, pkg, end) == -1 ==> (forall |k: int| 0 <= k < end ==> #[trigger] s[k] < pkg),
        (forall |k: int| 0 <= k < end ==> #[trigger] s[k] < pkg) ==> min_box_int(s, pkg, end) == -1,
        min_box_int(s, pkg, end) != -1 ==> (exists |k: int| 0 <= k < end && s[k] == min_box_int(s, pkg, end)),
        min_box_int(s, pkg, end) != -1 ==> min_box_int(s, pkg, end) >= pkg,
        forall |k: int| 0 <= k < end && #[trigger] s[k] >= pkg ==> min_box_int(s, pkg, end) != -1
            && s[k] >= min_box_int(s, pkg, end),
    decreases end
{
    if end > 0 {
        lemma_min_box_int_witness(s, pkg, end - 1);
        let prev = min_box_int(s, pkg, end - 1);
        let cur = s[end - 1];
        if cur >= pkg {
            if prev == -1 || cur <= prev {
                assert(min_box_int(s, pkg, end) == cur);
                assert(exists |k: int| 0 <= k < end && s[k] == cur) by {
                    assert(s[end - 1] == cur);
                }
            } else {
                assert(min_box_int(s, pkg, end) == prev);
            }
        } else {
            assert(min_box_int(s, pkg, end) == prev);
        }
    }
}

proof fn lemma_min_box_int_same_contains(s1: Seq<int>, s2: Seq<int>, pkg: int)
    requires
        forall |k: int| 0 <= k < s1.len() ==> #[trigger] s1[k] >= 0,
        forall |k: int| 0 <= k < s2.len() ==> #[trigger] s2[k] >= 0,
        forall |v: int| s1.contains(v) <==> s2.contains(v),
    ensures min_box_int(s1, pkg, s1.len() as int) == min_box_int(s2, pkg, s2.len() as int),
{
    lemma_min_box_int_witness(s1, pkg, s1.len() as int);
    lemma_min_box_int_witness(s2, pkg, s2.len() as int);
    let m1 = min_box_int(s1, pkg, s1.len() as int);
    let m2 = min_box_int(s2, pkg, s2.len() as int);
    if m1 == -1 && m2 != -1 {
        assert(s2.contains(m2));
        assert(s1.contains(m2));
        assert(exists |k: int| 0 <= k < s1.len() && s1[k] == m2) by {
            assert(s1.contains(m2));
        }
        let k = choose |k: int| 0 <= k < s1.len() && s1[k] == m2;
        assert(s1[k] < pkg);
        assert(s1[k] == m2);
        assert(m2 >= pkg);
    } else if m2 == -1 && m1 != -1 {
        assert(s1.contains(m1));
        assert(s2.contains(m1));
        let k = choose |k: int| 0 <= k < s2.len() && s2[k] == m1;
        assert(s2[k] < pkg);
        assert(m1 >= pkg);
    } else if m1 != -1 && m2 != -1 {
        assert(s1.contains(m1));
        assert(s2.contains(m1));
        let k = choose |k: int| 0 <= k < s2.len() && s2[k] == m1;
        assert(s2[k] >= pkg);
        assert(m2 <= s2[k]);
        assert(s2.contains(m2));
        assert(s1.contains(m2));
        let k2 = choose |k2: int| 0 <= k2 < s1.len() && s1[k2] == m2;
        assert(s1[k2] >= pkg);
        assert(m1 <= s1[k2]);
    }
}

proof fn lemma_merge_seq_contains(a: Seq<int>, b: Seq<int>, v: int)
    ensures merge_seq(a, b).contains(v) <==> (a.contains(v) || b.contains(v)),
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        assert(merge_seq(a, b) =~= b);
    } else if b.len() == 0 {
        assert(merge_seq(a, b) =~= a);
    } else if a[0] <= b[0] {
        lemma_merge_seq_contains(a.drop_first(), b, v);
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
        assert(a =~= seq![a[0]] + a.drop_first());
        assert((seq![a[0]] + merge_seq(a.drop_first(), b)).contains(v)
            <==> (seq![a[0]].contains(v) || merge_seq(a.drop_first(), b).contains(v))) by {
            lemma_seq_concat_contains_all_elements(seq![a[0]], merge_seq(a.drop_first(), b), v);
        }
        assert((seq![a[0]] + a.drop_first()).contains(v)
            <==> (seq![a[0]].contains(v) || a.drop_first().contains(v))) by {
            lemma_seq_concat_contains_all_elements(seq![a[0]], a.drop_first(), v);
        }
    } else {
        lemma_merge_seq_contains(a, b.drop_first(), v);
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
        assert(b =~= seq![b[0]] + b.drop_first());
        assert((seq![b[0]] + merge_seq(a, b.drop_first())).contains(v)
            <==> (seq![b[0]].contains(v) || merge_seq(a, b.drop_first()).contains(v))) by {
            lemma_seq_concat_contains_all_elements(seq![b[0]], merge_seq(a, b.drop_first()), v);
        }
        assert((seq![b[0]] + b.drop_first()).contains(v)
            <==> (seq![b[0]].contains(v) || b.drop_first().contains(v))) by {
            lemma_seq_concat_contains_all_elements(seq![b[0]], b.drop_first(), v);
        }
    }
}

proof fn lemma_merge_sort_seq_contains(s: Seq<int>, v: int)
    ensures merge_sort_seq(s).contains(v) <==> s.contains(v),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_contains(s.subrange(0, mid), v);
        lemma_merge_sort_seq_contains(s.subrange(mid, s.len() as int), v);
        lemma_merge_seq_contains(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), v);
        assert(s.contains(v) <==> (s.subrange(0, mid).contains(v) || s.subrange(mid, s.len() as int).contains(v))) by {
            lemma_seq_concat_contains_all_elements(s.subrange(0, mid), s.subrange(mid, s.len() as int), v);
            assert(s =~= s.subrange(0, mid) + s.subrange(mid, s.len() as int));
        }
    }
}

pub open spec fn scan_prev(sorted_bj: Seq<int>, idx: int) -> int {
    if idx <= 0 { 0int } else { sorted_bj[idx - 1] }
}

pub open spec fn scan_waste_partial(packages: Seq<i32>, sorted_bj: Seq<int>, box_idx: int, pkg_end: int) -> int
    decreases box_idx
{
    if box_idx <= 0 {
        0
    } else {
        let prev = scan_prev(sorted_bj, box_idx - 1);
        let b = sorted_bj[box_idx - 1];
        scan_waste_partial(packages, sorted_bj, box_idx - 1, pkg_end)
            + b * pkg_count_range(packages, pkg_end, prev + 1, b)
            - pkg_sum_range(packages, pkg_end, prev + 1, b)
    }
}

pub open spec fn point_bucket_contrib(sorted_bj: Seq<int>, v: int, box_idx: int) -> int
    decreases box_idx
{
    if box_idx <= 0 {
        0
    } else {
        let prev = scan_prev(sorted_bj, box_idx - 1);
        let b = sorted_bj[box_idx - 1];
        point_bucket_contrib(sorted_bj, v, box_idx - 1)
            + (if prev + 1 <= v && v <= b { b - v } else { 0int })
    }
}

proof fn lemma_point_bucket_char(sorted_bj: Seq<int>, v: int, box_idx: int)
    requires 0 <= box_idx <= sorted_bj.len(), sorted_asc(sorted_bj), v >= 1,
        forall |k: int| 0 <= k < sorted_bj.len() ==> #[trigger] sorted_bj[k] >= 0,
    ensures
        min_box_int(sorted_bj, v, box_idx) == -1 ==> point_bucket_contrib(sorted_bj, v, box_idx) == 0,
        min_box_int(sorted_bj, v, box_idx) != -1
            ==> point_bucket_contrib(sorted_bj, v, box_idx) == min_box_int(sorted_bj, v, box_idx) - v,
    decreases box_idx
{
    lemma_min_box_int_witness(sorted_bj, v, box_idx);
    if box_idx > 0 {
        lemma_point_bucket_char(sorted_bj, v, box_idx - 1);
        lemma_min_box_int_witness(sorted_bj, v, box_idx - 1);
        let prev_m = min_box_int(sorted_bj, v, box_idx - 1);
        let b = sorted_bj[box_idx - 1];
        let prev = scan_prev(sorted_bj, box_idx - 1);
        if prev_m != -1 {
            assert(exists |k: int| 0 <= k < box_idx - 1 && sorted_bj[k] == prev_m);
            let k = choose |k: int| 0 <= k < box_idx - 1 && sorted_bj[k] == prev_m;
            if box_idx >= 2 {
                assert(k <= box_idx - 2);
                assert(sorted_bj[k] <= sorted_bj[box_idx - 2]);
                assert(prev == sorted_bj[box_idx - 2]);
            } else {
                assert(k < 0);
            }
            assert(prev_m <= prev);
            assert(prev_m >= v);
            assert(!(prev + 1 <= v));
            assert(min_box_int(sorted_bj, v, box_idx) == prev_m);
        } else {
            if b >= v {
                assert(min_box_int(sorted_bj, v, box_idx) == b);
                if box_idx >= 2 {
                    assert(sorted_bj[box_idx - 2] < v);
                    assert(prev == sorted_bj[box_idx - 2]);
                } else {
                    assert(prev == 0);
                }
                assert(prev + 1 <= v);
            } else {
                assert(min_box_int(sorted_bj, v, box_idx) == -1);
                assert(!(v <= b));
            }
        }
    }
}

proof fn lemma_scan_waste_partial_step(packages: Seq<i32>, sorted_bj: Seq<int>, box_idx: int, pkg_end: int)
    requires 0 <= box_idx <= sorted_bj.len(), 0 <= pkg_end < packages.len(),
    ensures scan_waste_partial(packages, sorted_bj, box_idx, pkg_end + 1)
        == scan_waste_partial(packages, sorted_bj, box_idx, pkg_end)
            + point_bucket_contrib(sorted_bj, packages[pkg_end] as int, box_idx),
    decreases box_idx
{
    if box_idx > 0 {
        lemma_scan_waste_partial_step(packages, sorted_bj, box_idx - 1, pkg_end);
        let prev = scan_prev(sorted_bj, box_idx - 1);
        let b = sorted_bj[box_idx - 1];
        lemma_pkg_count_range_step(packages, pkg_end, prev + 1, b);
        lemma_pkg_sum_range_step(packages, pkg_end, prev + 1, b);
        let v = packages[pkg_end] as int;
        if prev + 1 <= v && v <= b {
            assert(b * (pkg_count_range(packages, pkg_end, prev + 1, b) + 1)
                == b * pkg_count_range(packages, pkg_end, prev + 1, b) + b) by (nonlinear_arith);
        }
    }
}

proof fn lemma_can_fit_upto_prefix(packages: Seq<i32>, boxes_j: Seq<i32>, end: int)
    requires 0 <= end <= packages.len(), Solution::can_fit_upto(packages, boxes_j, end), end > 0,
    ensures Solution::can_fit_upto(packages, boxes_j, end - 1),
{
}

proof fn lemma_sorted_max_witness(s: Seq<int>, v: int)
    requires sorted_asc(s), s.len() > 0,
    ensures
        (exists |k: int| 0 <= k < s.len() && s[k] >= v) <==> s[s.len() - 1] >= v,
{
}

proof fn lemma_scan_waste_partial_zero(packages: Seq<i32>, sorted_bj: Seq<int>, box_idx: int)
    requires 0 <= box_idx <= sorted_bj.len(),
    ensures scan_waste_partial(packages, sorted_bj, box_idx, 0) == 0,
    decreases box_idx
{
    if box_idx > 0 {
        lemma_scan_waste_partial_zero(packages, sorted_bj, box_idx - 1);
    }
}

proof fn lemma_scan_waste_eq_waste_upto(packages: Seq<i32>, boxes_j: Seq<i32>, sorted_bj: Seq<int>, pkg_end: int)
    requires
        0 <= pkg_end <= packages.len(),
        sorted_asc(sorted_bj),
        sorted_bj.len() == boxes_j.len(),
        forall |k: int| 0 <= k < sorted_bj.len() ==> #[trigger] sorted_bj[k] >= 1,
        forall |k: int| 0 <= k < boxes_j.len() ==> 1 <= #[trigger] boxes_j[k],
        forall |v: int| sorted_bj.contains(v) <==> to_int_seq(boxes_j).contains(v),
        forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] as int,
        Solution::can_fit_upto(packages, boxes_j, pkg_end),
    ensures scan_waste_partial(packages, sorted_bj, sorted_bj.len() as int, pkg_end) == Solution::waste_upto(packages, boxes_j, pkg_end),
    decreases pkg_end
{
    if pkg_end == 0 {
        lemma_scan_waste_partial_zero(packages, sorted_bj, sorted_bj.len() as int);
    } else {
        lemma_can_fit_upto_prefix(packages, boxes_j, pkg_end);
        lemma_scan_waste_eq_waste_upto(packages, boxes_j, sorted_bj, pkg_end - 1);
        lemma_scan_waste_partial_step(packages, sorted_bj, sorted_bj.len() as int, pkg_end - 1);
        let pkg = packages[pkg_end - 1];
        let v = pkg as int;
        lemma_min_box_int_eq_min_box_upto(boxes_j, pkg, boxes_j.len() as int);
        assert(forall |k: int| 0 <= k < to_int_seq(boxes_j).len() ==> #[trigger] to_int_seq(boxes_j)[k] >= 0) by {
            assert forall |k: int| 0 <= k < to_int_seq(boxes_j).len() implies #[trigger] to_int_seq(boxes_j)[k] >= 0 by {
                assert(to_int_seq(boxes_j)[k] == boxes_j[k] as int);
            }
        }
        lemma_min_box_int_same_contains(to_int_seq(boxes_j), sorted_bj, v);
        lemma_point_bucket_char(sorted_bj, v, sorted_bj.len() as int);
        assert(Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) >= pkg as int);
        assert(min_box_int(sorted_bj, v, sorted_bj.len() as int) != -1);
        assert(point_bucket_contrib(sorted_bj, v, sorted_bj.len() as int)
            == Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) - v);
        assert(Solution::waste_upto(packages, boxes_j, pkg_end)
            == (Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) - v)
                + Solution::waste_upto(packages, boxes_j, pkg_end - 1));
        assert(scan_waste_partial(packages, sorted_bj, sorted_bj.len() as int, pkg_end)
            == Solution::waste_upto(packages, boxes_j, pkg_end));
    }
}

proof fn lemma_can_fit_iff_max_box(packages: Seq<i32>, boxes_j: Seq<i32>, sorted_bj: Seq<int>, end: int)
    requires
        0 <= end <= packages.len(),
        sorted_asc(sorted_bj),
        sorted_bj.len() == boxes_j.len(),
        sorted_bj.len() > 0,
        forall |k: int| 0 <= k < sorted_bj.len() ==> #[trigger] sorted_bj[k] >= 1,
        forall |k: int| 0 <= k < boxes_j.len() ==> 1 <= #[trigger] boxes_j[k],
        forall |v: int| sorted_bj.contains(v) <==> to_int_seq(boxes_j).contains(v),
        forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] as int <= 100_000,
    ensures
        Solution::can_fit_upto(packages, boxes_j, end)
            <==> pkg_count_range(packages, end, sorted_bj[sorted_bj.len() - 1] + 1, 100_000) == 0,
    decreases end
{
    if end > 0 {
        lemma_can_fit_iff_max_box(packages, boxes_j, sorted_bj, end - 1);
        lemma_pkg_count_range_step(packages, end - 1, sorted_bj[sorted_bj.len() - 1] + 1, 100_000);
        lemma_pkg_count_range_nonneg(packages, end - 1, sorted_bj[sorted_bj.len() - 1] + 1, 100_000);
        let pkg = packages[end - 1];
        let v = pkg as int;
        lemma_min_box_int_eq_min_box_upto(boxes_j, pkg, boxes_j.len() as int);
        assert(forall |k: int| 0 <= k < to_int_seq(boxes_j).len() ==> #[trigger] to_int_seq(boxes_j)[k] >= 0) by {
            assert forall |k: int| 0 <= k < to_int_seq(boxes_j).len() implies #[trigger] to_int_seq(boxes_j)[k] >= 0 by {
                assert(to_int_seq(boxes_j)[k] == boxes_j[k] as int);
            }
        }
        lemma_min_box_int_same_contains(to_int_seq(boxes_j), sorted_bj, v);
        lemma_min_box_int_witness(sorted_bj, v, sorted_bj.len() as int);
        lemma_sorted_max_witness(sorted_bj, v);
        assert(Solution::can_fit_upto(packages, boxes_j, end)
            == (Solution::can_fit_upto(packages, boxes_j, end - 1)
                && Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) >= v));
        assert(Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) >= v
            <==> Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) != -1);
        assert(Solution::min_box_upto(boxes_j, pkg, boxes_j.len() as int) != -1
            <==> sorted_bj[sorted_bj.len() - 1] >= v);
        assert(pkg_count_range(packages, end, sorted_bj[sorted_bj.len() - 1] + 1, 100_000)
            == pkg_count_range(packages, end - 1, sorted_bj[sorted_bj.len() - 1] + 1, 100_000)
                + (if sorted_bj[sorted_bj.len() - 1] + 1 <= v && v <= 100_000 { 1int } else { 0int }));
        assert(v <= 100_000);
        assert((sorted_bj[sorted_bj.len() - 1] + 1 <= v && v <= 100_000)
            <==> !(sorted_bj[sorted_bj.len() - 1] >= v));
        assert(Solution::can_fit_upto(packages, boxes_j, end)
            <==> pkg_count_range(packages, end, sorted_bj[sorted_bj.len() - 1] + 1, 100_000) == 0);
    }
}

proof fn lemma_sorted_bj_props(boxes_j: Seq<i32>)
    requires forall |k: int| 0 <= k < boxes_j.len() ==> 1 <= #[trigger] boxes_j[k] <= 100_000,
    ensures
        sorted_asc(merge_sort_seq(to_int_seq(boxes_j))),
        merge_sort_seq(to_int_seq(boxes_j)).len() == boxes_j.len(),
        forall |v: int| merge_sort_seq(to_int_seq(boxes_j)).contains(v) <==> to_int_seq(boxes_j).contains(v),
        forall |k: int| 0 <= k < merge_sort_seq(to_int_seq(boxes_j)).len()
            ==> 1 <= #[trigger] merge_sort_seq(to_int_seq(boxes_j))[k] <= 100_000,
{
    let sorted_bj = merge_sort_seq(to_int_seq(boxes_j));
    lemma_merge_sort_seq_sorted(to_int_seq(boxes_j));
    lemma_merge_sort_seq_len(to_int_seq(boxes_j));
    assert forall |v: int| #[trigger] sorted_bj.contains(v) <==> to_int_seq(boxes_j).contains(v) by {
        lemma_merge_sort_seq_contains(to_int_seq(boxes_j), v);
    }
    assert forall |k: int| 0 <= k < sorted_bj.len() implies 1 <= #[trigger] sorted_bj[k] <= 100_000 by {
        assert(sorted_bj.contains(sorted_bj[k]));
        assert(to_int_seq(boxes_j).contains(sorted_bj[k]));
        assert(exists |j: int| 0 <= j < boxes_j.len() && to_int_seq(boxes_j)[j] == sorted_bj[k]);
        let j = choose |j: int| 0 <= j < boxes_j.len() && to_int_seq(boxes_j)[j] == sorted_bj[k];
        assert(to_int_seq(boxes_j)[j] == boxes_j[j] as int);
    }
}

proof fn lemma_merge_seq_skip_step_a(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires 0 <= i < a.len(), 0 <= j <= b.len(), (j >= b.len() || a[i] <= b[j]),
    ensures merge_seq(a.skip(i), b.skip(j)) =~= seq![a[i]] + merge_seq(a.skip(i + 1), b.skip(j)),
{
    assert(a.skip(i)[0] == a[i]);
    assert(a.skip(i).drop_first() =~= a.skip(i + 1));
    if j < b.len() {
        assert(b.skip(j)[0] == b[j]);
        assert(a.skip(i)[0] <= b.skip(j)[0]);
    } else {
        assert(b.skip(j).len() == 0);
    }
}

proof fn lemma_merge_seq_skip_step_b(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires 0 <= i <= a.len(), 0 <= j < b.len(), (i >= a.len() || b[j] < a[i]),
    ensures merge_seq(a.skip(i), b.skip(j)) =~= seq![b[j]] + merge_seq(a.skip(i), b.skip(j + 1)),
{
    assert(b.skip(j)[0] == b[j]);
    assert(b.skip(j).drop_first() =~= b.skip(j + 1));
    if i < a.len() {
        assert(a.skip(i)[0] == a[i]);
        assert(b.skip(j)[0] < a.skip(i)[0]);
    } else {
        assert(a.skip(i).len() == 0);
    }
}

fn merge_exec(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted_asc(to_int_seq(a@)),
        sorted_asc(to_int_seq(b@)),
    ensures
        to_int_seq(result@) == merge_seq(to_int_seq(a@), to_int_seq(b@)),
{
    let ghost av = to_int_seq(a@);
    let ghost bv = to_int_seq(b@);
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(av.skip(0) =~= av);
        assert(bv.skip(0) =~= bv);
        assert(to_int_seq(result@) =~= Seq::<int>::empty());
    }
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j,
            to_int_seq(a@) == av,
            to_int_seq(b@) == bv,
            to_int_seq(result@) + merge_seq(av.skip(i as int), bv.skip(j as int)) == merge_seq(av, bv),
        decreases (a.len() - i) + (b.len() - j),
    {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            proof {
                lemma_merge_seq_skip_step_a(av, bv, i as int, j as int);
                assert(to_int_seq(result@).push(a@[i as int] as int) =~= to_int_seq(result@) + seq![a@[i as int] as int]);
            }
            result.push(a[i]);
            i += 1;
        } else {
            proof {
                lemma_merge_seq_skip_step_b(av, bv, i as int, j as int);
                assert(to_int_seq(result@).push(b@[j as int] as int) =~= to_int_seq(result@) + seq![b@[j as int] as int]);
            }
            result.push(b[j]);
            j += 1;
        }
    }
    proof {
        assert(av.skip(i as int).len() == 0);
        assert(bv.skip(j as int).len() == 0);
        assert(merge_seq(av.skip(i as int), bv.skip(j as int)) =~= Seq::<int>::empty());
        assert(to_int_seq(result@) == merge_seq(av, bv));
    }
    result
}

fn merge_sort_exec(v: &Vec<i32>) -> (result: Vec<i32>)
    requires v.len() <= 100_000,
    ensures to_int_seq(result@) == merge_sort_seq(to_int_seq(v@)),
    decreases v.len()
{
    if v.len() <= 1 {
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < v.len()
            invariant k <= v.len(), result@.len() == k as int,
                forall |t: int| 0 <= t < k ==> result@[t] == v@[t],
            decreases v.len() - k,
        {
            result.push(v[k]);
            k += 1;
        }
        proof {
            assert(result@ =~= v@);
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant i <= mid, mid <= v.len(), left@.len() == i as int,
                forall |t: int| 0 <= t < i ==> left@[t] == v@[t],
            decreases mid - i,
        {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len()
            invariant mid <= i2 <= v.len(), right@.len() == i2 - mid,
                forall |t: int| 0 <= t < i2 - mid ==> right@[t as int] == v@[t + mid as int],
            decreases v.len() - i2,
        {
            right.push(v[i2]);
            i2 += 1;
        }
        proof {
            assert(left@ =~= v@.subrange(0, mid as int));
            assert(right@ =~= v@.subrange(mid as int, v@.len() as int));
        }
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        proof {
            lemma_merge_sort_seq_sorted(to_int_seq(v@).subrange(0, mid as int));
            lemma_merge_sort_seq_sorted(to_int_seq(v@).subrange(mid as int, v@.len() as int));
            assert(to_int_seq(left@) =~= to_int_seq(v@).subrange(0, mid as int));
            assert(to_int_seq(right@) =~= to_int_seq(v@).subrange(mid as int, v@.len() as int));
        }
        let result = merge_exec(&sorted_left, &sorted_right);
        proof {
            assert(to_int_seq(result@) == merge_seq(to_int_seq(sorted_left@), to_int_seq(sorted_right@)));
            assert(merge_sort_seq(to_int_seq(v@)) ==
                merge_seq(merge_sort_seq(to_int_seq(v@).subrange(0, mid as int)),
                    merge_sort_seq(to_int_seq(v@).subrange(mid as int, v@.len() as int))));
        }
        result
    }
}

proof fn lemma_min_box_upto_bound(boxes_j: Seq<i32>, pkg: i32, end: int)
    requires 0 <= end <= boxes_j.len(),
        forall |k: int| 0 <= k < boxes_j.len() ==> #[trigger] boxes_j[k] as int <= 100_000,
    ensures Solution::min_box_upto(boxes_j, pkg, end) <= 100_000,
    decreases end
{
    if end > 0 {
        lemma_min_box_upto_bound(boxes_j, pkg, end - 1);
    }
}

proof fn lemma_pkg_count_range_zero_when_all_ge_one(packages: Seq<i32>, end: int)
    requires 0 <= end <= packages.len(), forall |k: int| 0 <= k < end ==> #[trigger] packages[k] >= 1,
    ensures pkg_count_range(packages, end, 0, 0) == 0,
    decreases end
{
    if end > 0 {
        lemma_pkg_count_range_zero_when_all_ge_one(packages, end - 1);
    }
}

proof fn lemma_pkg_sum_range_le_hi_times_count(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= packages.len(), hi >= 0, lo >= 0,
    ensures 0 <= pkg_sum_range(packages, end, lo, hi) <= hi * pkg_count_range(packages, end, lo, hi),
    decreases end
{
    if end > 0 {
        lemma_pkg_sum_range_le_hi_times_count(packages, end - 1, lo, hi);
        if lo <= packages[end - 1] && packages[end - 1] as int <= hi {
            assert(hi * pkg_count_range(packages, end - 1, lo, hi) + hi
                == hi * (pkg_count_range(packages, end - 1, lo, hi) + 1)) by (nonlinear_arith);
        }
    }
}

proof fn lemma_scan_waste_partial_bound(packages: Seq<i32>, sorted_bj: Seq<int>, box_idx: int, pkg_end: int)
    requires 0 <= box_idx <= sorted_bj.len(), 0 <= pkg_end <= packages.len(),
        forall |k: int| 0 <= k < sorted_bj.len() ==> 0 <= #[trigger] sorted_bj[k] <= 100_000,
    ensures 0 <= scan_waste_partial(packages, sorted_bj, box_idx, pkg_end) <= 100_000 * pkg_end * box_idx,
    decreases box_idx
{
    if box_idx > 0 {
        lemma_scan_waste_partial_bound(packages, sorted_bj, box_idx - 1, pkg_end);
        let prev = scan_prev(sorted_bj, box_idx - 1);
        let b = sorted_bj[box_idx - 1];
        lemma_pkg_sum_range_le_hi_times_count(packages, pkg_end, prev + 1, b);
        lemma_pkg_count_range_nonneg(packages, pkg_end, prev + 1, b);
        assert(pkg_count_range(packages, pkg_end, prev + 1, b) <= pkg_end);
        assert(b * pkg_count_range(packages, pkg_end, prev + 1, b) <= 100_000 * pkg_end) by (nonlinear_arith)
            requires b <= 100_000, 0 <= pkg_count_range(packages, pkg_end, prev + 1, b) <= pkg_end;
        assert(100_000 * pkg_end * (box_idx - 1) + 100_000 * pkg_end == 100_000 * pkg_end * box_idx) by (nonlinear_arith);
    }
}

proof fn lemma_pkg_sum_range_bound_by_full(packages: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= packages.len(),
        forall |k: int| 0 <= k < packages.len() ==> 0 <= #[trigger] packages[k] as int <= 100_000,
    ensures 0 <= pkg_sum_range(packages, end, lo, hi) <= 100_000 * end,
    decreases end
{
    if end > 0 {
        lemma_pkg_sum_range_bound_by_full(packages, end - 1, lo, hi);
        if lo <= packages[end - 1] && packages[end - 1] as int <= hi {
            assert(100_000 * (end - 1) + 100_000 == 100_000 * end) by (nonlinear_arith);
        }
    }
}

proof fn lemma_pkg_sum_range_eq_val_times_count(packages: Seq<i32>, end: int, v: int)
    requires 0 <= end <= packages.len(),
    ensures pkg_sum_range(packages, end, v, v) == v * pkg_count_range(packages, end, v, v),
    decreases end
{
    if end > 0 {
        lemma_pkg_sum_range_eq_val_times_count(packages, end - 1, v);
        if v <= packages[end - 1] && packages[end - 1] as int <= v {
            assert(packages[end - 1] as int == v);
            assert(v * pkg_count_range(packages, end - 1, v, v) + v
                == v * (pkg_count_range(packages, end - 1, v, v) + 1)) by (nonlinear_arith);
        }
    }
}

proof fn lemma_waste_upto_bound(packages: Seq<i32>, boxes_j: Seq<i32>, end: int)
    requires 0 <= end <= packages.len(),
        forall |k: int| 0 <= k < boxes_j.len() ==> #[trigger] boxes_j[k] as int <= 100_000,
        forall |i: int| 0 <= i < packages.len() ==> 0 <= #[trigger] packages[i] as int,
        Solution::can_fit_upto(packages, boxes_j, end),
    ensures 0 <= Solution::waste_upto(packages, boxes_j, end) <= 100_000 * end,
    decreases end
{
    if end > 0 {
        lemma_can_fit_upto_prefix(packages, boxes_j, end);
        lemma_waste_upto_bound(packages, boxes_j, end - 1);
        lemma_min_box_upto_bound(boxes_j, packages[end - 1], boxes_j.len() as int);
        assert(100_000 * (end - 1) + 100_000 == 100_000 * end) by (nonlinear_arith);
    }
}

impl Solution {
    pub fn min_wasted_space(packages: Vec<i32>, boxes: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= packages.len() <= 100_000,
            forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
            1 <= boxes.len() <= 100_000,
            forall |j: int| #![trigger boxes@[j]] 0 <= j < boxes@.len() ==> 1 <= boxes@[j]@.len() <= 100_000,
            forall |j: int, k: int| 0 <= j < boxes@.len() && 0 <= k < boxes@[j]@.len()
                ==> 1 <= #[trigger] boxes@[j]@[k] <= 100_000,
            1 <= Self::total_boxes_len(boxes@, boxes@.len() as int) <= 100_000,
            forall |j: int, k1: int, k2: int| 0 <= j < boxes@.len() && 0 <= k1 < k2 < boxes@[j]@.len()
                ==> boxes@[j]@[k1] != boxes@[j]@[k2],
        ensures
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) == -1 ==> res == -1i32,
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) >= 0 ==>
                res == (Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) % 1_000_000_007) as i32,
    {
        let n = packages.len();
        let m = boxes.len();
        let modulo: i64 = 1_000_000_007;

        let mut pkg_count: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 100_000
            invariant
                pkg_count@.len() == vi as int,
                0 <= vi <= 100_001,
                forall |v: int| 0 <= v < vi as int ==> (#[trigger] pkg_count@[v]) as int == pkg_count_range(packages@, 0, v, v),
            decreases 100_001 - vi,
        {
            pkg_count.push(0);
            vi += 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == packages.len(),
                1 <= packages.len() <= 100_000,
                pkg_count@.len() == 100_001,
                forall |k: int| 0 <= k < packages.len() ==> 1 <= #[trigger] packages@[k] <= 100_000,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] pkg_count@[v]) as int == pkg_count_range(packages@, i as int, v, v),
                forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] pkg_count@[v] <= i as i64,
            decreases n - i,
        {
            let val = packages[i] as usize;
            proof {
                lemma_pkg_count_range_step(packages@, i as int, val as int, val as int);
                assert forall |v: int| 0 <= v <= 100_000 && v != val as int implies
                    (#[trigger] pkg_count@[v]) as int == pkg_count_range(packages@, i as int + 1, v, v) by {
                    lemma_pkg_count_range_step(packages@, i as int, v, v);
                    assert(!(v <= packages@[i as int] && packages@[i as int] as int <= v));
                }
            }
            let ghost pkg_count_before = pkg_count@;
            pkg_count.set(val, pkg_count[val] + 1);
            proof {
                assert(pkg_count@ =~= pkg_count_before.update(val as int, (pkg_count_before[val as int] + 1) as i64));
            }
            i += 1;
        }

        let mut pkg_count_prefix: Vec<i64> = Vec::new();
        pkg_count_prefix.push(pkg_count[0]);
        let mut pkg_sum_prefix: Vec<i64> = Vec::new();
        proof {
            assert forall |k: int| 0 <= k < n as int implies #[trigger] packages@[k] >= 1 by {
                assert(1 <= packages@[k] <= 100_000);
            }
            lemma_pkg_count_range_zero_when_all_ge_one(packages@, n as int);
            lemma_pkg_sum_range_eq_val_times_count(packages@, n as int, 0);
        }
        pkg_sum_prefix.push(0);
        let mut v1: usize = 1;
        while v1 <= 100_000
            invariant
                pkg_count_prefix@.len() == v1 as int,
                pkg_sum_prefix@.len() == v1 as int,
                1 <= v1 <= 100_001,
                n == packages.len(),
                1 <= packages.len() <= 100_000,
                forall |k: int| 0 <= k < packages.len() ==> 1 <= #[trigger] packages@[k] <= 100_000,
                pkg_count@.len() == 100_001,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] pkg_count@[v]) as int == pkg_count_range(packages@, n as int, v, v),
                forall |v: int| 0 <= v < v1 as int ==> (#[trigger] pkg_count_prefix@[v]) as int == pkg_count_range(packages@, n as int, 0, v),
                forall |v: int| 0 <= v < v1 as int ==> 0 <= #[trigger] pkg_count_prefix@[v] <= n as i64,
                forall |v: int| 0 <= v < v1 as int ==> (#[trigger] pkg_sum_prefix@[v]) as int == pkg_sum_range(packages@, n as int, 0, v),
                forall |v: int| 0 <= v < v1 as int ==> 0 <= #[trigger] pkg_sum_prefix@[v] <= 100_000 * n as i64,
            decreases 100_001 - v1,
        {
            proof {
                lemma_pkg_count_range_nonneg(packages@, n as int, 0, v1 as int);
                lemma_pkg_count_range_split(packages@, n as int, 0, v1 as int - 1, v1 as int);
                assert(pkg_count_prefix@[v1 as int - 1] as int + pkg_count@[v1 as int] as int <= n as int);
                lemma_pkg_sum_range_split(packages@, n as int, 0, v1 as int - 1, v1 as int);
                lemma_pkg_sum_range_eq_val_times_count(packages@, n as int, v1 as int);
                lemma_pkg_count_range_nonneg(packages@, n as int, v1 as int, v1 as int);
                assert forall |k: int| 0 <= k < packages@.len() implies 0 <= #[trigger] packages@[k] as int <= 100_000 by {
                    assert(1 <= packages[k] <= 100_000);
                }
                lemma_pkg_sum_range_bound_by_full(packages@, n as int, 0, v1 as int);
                assert(pkg_sum_prefix@[v1 as int - 1] as int + (v1 as int) * pkg_count@[v1 as int] as int <= 100_000 * n as int);
            }
            let next_count = pkg_count_prefix[v1 - 1] + pkg_count[v1];
            pkg_count_prefix.push(next_count);
            let next_sum = pkg_sum_prefix[v1 - 1] + (v1 as i64) * pkg_count[v1];
            pkg_sum_prefix.push(next_sum);
            v1 += 1;
        }

        let mut best: i64 = -1;
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                m == boxes.len(),
                1 <= boxes.len() <= 100_000,
                n == packages.len(),
                1 <= packages.len() <= 100_000,
                pkg_count_prefix@.len() == 100_001,
                pkg_sum_prefix@.len() == 100_001,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] pkg_count_prefix@[v]) as int == pkg_count_range(packages@, n as int, 0, v),
                forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] pkg_count_prefix@[v] <= n as i64,
                forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] pkg_sum_prefix@[v]) as int == pkg_sum_range(packages@, n as int, 0, v),
                forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] pkg_sum_prefix@[v] <= 100_000 * n as i64,
                forall |k: int| 0 <= k < packages.len() ==> 1 <= #[trigger] packages@[k] <= 100_000,
                forall |jj: int| #![trigger boxes@[jj]] 0 <= jj < boxes@.len() ==> 1 <= boxes@[jj]@.len() <= 100_000,
                forall |jj: int, k: int| 0 <= jj < boxes@.len() && 0 <= k < boxes@[jj]@.len()
                    ==> 1 <= #[trigger] boxes@[jj]@[k] <= 100_000,
                forall |jj: int, k1: int, k2: int| 0 <= jj < boxes@.len() && 0 <= k1 < k2 < boxes@[jj]@.len()
                    ==> boxes@[jj]@[k1] != boxes@[jj]@[k2],
                -1 <= best <= 2_000_000_000_000_000i64,
                best as int == Solution::best_waste_upto(packages@, boxes@, j as int),
            decreases m - j,
        {
            let sorted_bj = merge_sort_exec(&boxes[j]);
            proof {
                lemma_sorted_bj_props(boxes@[j as int]@);
                assert(boxes@[j as int]@.len() <= 100_000);
            }
            let bj_len = sorted_bj.len();
            let mut waste: i64 = 0;
            let mut prev: usize = 0;
            let mut t: usize = 0;
            while t < bj_len
                invariant
                    0 <= t <= bj_len,
                    bj_len <= 100_000,
                    bj_len == sorted_bj.len(),
                    n == packages.len(),
                    1 <= packages.len() <= 100_000,
                    pkg_count_prefix@.len() == 100_001,
                    pkg_sum_prefix@.len() == 100_001,
                    forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] pkg_count_prefix@[v]) as int == pkg_count_range(packages@, n as int, 0, v),
                    forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] pkg_count_prefix@[v] <= n as i64,
                    forall |v: int| 0 <= v <= 100_000 ==> (#[trigger] pkg_sum_prefix@[v]) as int == pkg_sum_range(packages@, n as int, 0, v),
                    forall |v: int| 0 <= v <= 100_000 ==> 0 <= #[trigger] pkg_sum_prefix@[v] <= 100_000 * n as i64,
                    sorted_asc(to_int_seq(sorted_bj@)),
                    forall |k: int| 0 <= k < sorted_bj.len() ==> 1 <= #[trigger] to_int_seq(sorted_bj@)[k] <= 100_000,
                    waste as int == scan_waste_partial(packages@, to_int_seq(sorted_bj@), t as int, n as int),
                    prev as int == scan_prev(to_int_seq(sorted_bj@), t as int),
                    0 <= waste <= 2_000_000_000_000_000i64,
                    0 <= prev <= 100_000,
                decreases bj_len - t,
            {
                let b = sorted_bj[t];
                let bu = b as usize;
                proof {
                    assert(to_int_seq(sorted_bj@)[t as int] == bu as int);
                    if t > 0 {
                        assert(to_int_seq(sorted_bj@)[t as int - 1] <= to_int_seq(sorted_bj@)[t as int]);
                    }
                    assert(prev <= bu);
                    lemma_pkg_count_range_nonneg(packages@, n as int, 0, prev as int);
                    lemma_pkg_count_range_split(packages@, n as int, 0, prev as int, bu as int);
                    lemma_pkg_sum_range_split(packages@, n as int, 0, prev as int, bu as int);
                    lemma_pkg_count_range_nonneg(packages@, n as int, prev as int + 1, bu as int);
                    assert(scan_waste_partial(packages@, to_int_seq(sorted_bj@), t as int + 1, n as int)
                        == scan_waste_partial(packages@, to_int_seq(sorted_bj@), t as int, n as int)
                            + (bu as int) * pkg_count_range(packages@, n as int, prev as int + 1, bu as int)
                            - pkg_sum_range(packages@, n as int, prev as int + 1, bu as int));
                    assert forall |k: int| 0 <= k < sorted_bj.len() implies
                        0 <= #[trigger] to_int_seq(sorted_bj@)[k] <= 100_000 by {
                        assert(1 <= to_int_seq(sorted_bj@)[k] <= 100_000);
                    }
                    lemma_scan_waste_partial_bound(packages@, to_int_seq(sorted_bj@), t as int + 1, n as int);
                    assert(100_000 * (n as int) * (t as int + 1) <= 2_000_000_000_000_000) by (nonlinear_arith)
                        requires n as int <= 100_000, t as int + 1 <= 100_000;
                }
                let cnt = pkg_count_prefix[bu] - pkg_count_prefix[prev];
                let sm = pkg_sum_prefix[bu] - pkg_sum_prefix[prev];
                waste = waste + (bu as i64) * cnt - sm;
                prev = bu;
                t += 1;
            }
            let remaining = pkg_count_prefix[100_000] - pkg_count_prefix[prev];
            let can_fit = remaining == 0;
            proof {
                lemma_can_fit_iff_max_box(packages@, boxes@[j as int]@, to_int_seq(sorted_bj@), n as int);
                assert(prev as int == to_int_seq(sorted_bj@)[sorted_bj@.len() as int - 1]);
                lemma_pkg_count_range_nonneg(packages@, n as int, prev as int + 1, 100_000);
                lemma_pkg_count_range_split(packages@, n as int, 0, prev as int, 100_000);
            }
            if can_fit {
                proof {
                    lemma_waste_upto_bound(packages@, boxes@[j as int]@, n as int);
                    lemma_scan_waste_eq_waste_upto(packages@, boxes@[j as int]@, to_int_seq(sorted_bj@), n as int);
                }
                if best == -1 || waste < best {
                    best = waste;
                }
            }
            j += 1;
        }

        if best == -1 {
            -1
        } else {
            (best % modulo) as i32
        }
    }
}

}
