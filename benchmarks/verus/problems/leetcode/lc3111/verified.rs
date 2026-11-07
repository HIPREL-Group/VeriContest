use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn x_prefix(points: Seq<Vec<i32>>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else if end > points.len() {
            Self::x_prefix(points, points.len() as int)
        } else {
            Self::x_prefix(points, end - 1).push(points[end - 1][0])
        }
    }

    pub open spec fn x_seq(points: Seq<Vec<i32>>) -> Seq<i32> {
        Self::x_prefix(points, points.len() as int)
    }

    pub open spec fn min_rectangles_continue(s: Seq<i32>, w: int, start: int, cover: int) -> int
        decreases s.len() - start,
    {
        if start < 0 {
            Self::min_rectangles_continue(s, w, 0, cover)
        } else if start >= s.len() {
            0
        } else if s[start] as int <= cover {
            Self::min_rectangles_continue(s, w, start + 1, cover)
        } else {
            1 + Self::min_rectangles_continue(s, w, start + 1, s[start] as int + w)
        }
    }

    pub open spec fn min_rectangles_sorted_from(s: Seq<i32>, w: int, start: int) -> int
        decreases s.len() - start,
    {
        if start < 0 {
            Self::min_rectangles_sorted_from(s, w, 0)
        } else if start >= s.len() {
            0
        } else {
            1 + Self::min_rectangles_continue(s, w, start + 1, s[start] as int + w)
        }
    }

    proof fn lemma_continue_skip_prefix(s: Seq<i32>, w: int, start: int, cover: int, end: int)
        requires
            0 <= start <= end <= s.len(),
            forall|k: int| start <= k < end ==> s[k] as int <= cover,
        ensures
            Self::min_rectangles_continue(s, w, start, cover) == Self::min_rectangles_continue(s, w, end, cover),
        decreases end - start,
    {
        if start < end {
            assert(start < s.len());
            assert(s[start] as int <= cover);
            Self::lemma_continue_skip_prefix(s, w, start + 1, cover, end);
            assert(Self::min_rectangles_continue(s, w, start, cover) == Self::min_rectangles_continue(s, w, start + 1, cover));
        } else {
        }
    }

    proof fn lemma_continue_at_gt_equals_sorted(s: Seq<i32>, w: int, start: int, cover: int)
        requires
            0 <= start < s.len(),
            s[start] as int > cover,
        ensures
            Self::min_rectangles_continue(s, w, start, cover) == Self::min_rectangles_sorted_from(s, w, start),
    {
    }
}

pub open spec fn encode(v: int, i: int) -> int {
    v * 200000 + i
}

pub open spec fn decode_idx(e: int) -> int {
    e % 200000
}

pub open spec fn decode_val(e: int) -> int {
    e / 200000
}

proof fn lemma_encode_decode_idx(v: int, i: int)
    requires 0 <= i < 200000,
    ensures decode_idx(encode(v, i)) == i,
{
    assert(encode(v, i) == v * 200000 + i);
}

proof fn lemma_encode_decode_val(v: int, i: int)
    requires 0 <= i < 200000,
    ensures decode_val(encode(v, i)) == v,
{
    assert(encode(v, i) == v * 200000 + i);
}

proof fn lemma_encode_order(v1: int, i1: int, v2: int, i2: int)
    requires 0 <= i1 < 200000, 0 <= i2 < 200000,
    ensures
        encode(v1, i1) < encode(v2, i2) <==> (v1 < v2 || (v1 == v2 && i1 < i2)),
        encode(v1, i1) == encode(v2, i2) <==> (v1 == v2 && i1 == i2),
{
    if v1 < v2 {
        assert(encode(v1, i1) < encode(v2, i2)) by (nonlinear_arith)
            requires v1 < v2, 0 <= i1 < 200000, 0 <= i2 < 200000;
    } else if v1 > v2 {
        assert(encode(v1, i1) > encode(v2, i2)) by (nonlinear_arith)
            requires v1 > v2, 0 <= i1 < 200000, 0 <= i2 < 200000;
    }
}

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|a: int, b: int| 0 <= a <= b < s.len() ==> s[a] <= s[b]
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

proof fn lemma_sorted_drop_first(s: Seq<int>)
    requires sorted_asc(s), s.len() >= 1,
    ensures sorted_asc(s.drop_first()),
{
    assert forall |a: int, b: int| 0 <= a <= b < s.drop_first().len() implies
        s.drop_first()[a] <= s.drop_first()[b] by {
        assert(s.drop_first()[a] == s[a + 1]);
        assert(s.drop_first()[b] == s[b + 1]);
    }
}

proof fn lemma_sorted_cons(x: int, rest: Seq<int>)
    requires sorted_asc(rest), rest.len() == 0 || x <= rest[0],
    ensures sorted_asc(seq![x] + rest),
{
    assert forall |a: int, b: int| 0 <= a <= b < (seq![x] + rest).len() implies
        (seq![x] + rest)[a] <= (seq![x] + rest)[b] by {
        if a == 0 {
            if b > 0 {
                assert((seq![x] + rest)[b] == rest[b - 1]);
                if b > 1 {
                    assert(rest[0] <= rest[b - 1]);
                }
            }
        } else {
            assert((seq![x] + rest)[a] == rest[a - 1]);
            assert((seq![x] + rest)[b] == rest[b - 1]);
        }
    }
}

proof fn lemma_merge_seq_all_ge(a: Seq<int>, b: Seq<int>, lo: int)
    requires
        forall |i: int| 0 <= i < a.len() ==> lo <= a[i],
        forall |i: int| 0 <= i < b.len() ==> lo <= b[i],
    ensures forall |i: int| 0 <= i < merge_seq(a, b).len() ==> lo <= #[trigger] merge_seq(a, b)[i],
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_all_ge(a.drop_first(), b, lo);
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
    } else {
        lemma_merge_seq_all_ge(a, b.drop_first(), lo);
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
    }
}

proof fn lemma_merge_seq_sorted(a: Seq<int>, b: Seq<int>)
    requires sorted_asc(a), sorted_asc(b),
    ensures sorted_asc(merge_seq(a, b)),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_sorted_drop_first(a);
        lemma_merge_seq_sorted(a.drop_first(), b);
        if merge_seq(a.drop_first(), b).len() > 0 {
            if a.drop_first().len() > 0 {
                assert(a[0] <= a.drop_first()[0]);
            }
            lemma_merge_seq_all_ge(a.drop_first(), b, a[0]);
        }
        lemma_sorted_cons(a[0], merge_seq(a.drop_first(), b));
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
    } else {
        lemma_sorted_drop_first(b);
        lemma_merge_seq_sorted(a, b.drop_first());
        if merge_seq(a, b.drop_first()).len() > 0 {
            if b.drop_first().len() > 0 {
                assert(b[0] <= b.drop_first()[0]);
            }
            lemma_merge_seq_all_ge(a, b.drop_first(), b[0]);
        }
        lemma_sorted_cons(b[0], merge_seq(a, b.drop_first()));
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
    }
}

proof fn lemma_merge_seq_len(a: Seq<int>, b: Seq<int>)
    ensures merge_seq(a, b).len() == a.len() + b.len(),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_len(a.drop_first(), b);
    } else {
        lemma_merge_seq_len(a, b.drop_first());
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
    if s.len() > 1 {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_sorted(s.subrange(0, mid));
        lemma_merge_sort_seq_sorted(s.subrange(mid, s.len() as int));
        lemma_merge_seq_sorted(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
    }
}

proof fn lemma_merge_sort_seq_len(s: Seq<int>)
    ensures merge_sort_seq(s).len() == s.len(),
    decreases s.len()
{
    if s.len() > 1 {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_len(s.subrange(0, mid));
        lemma_merge_sort_seq_len(s.subrange(mid, s.len() as int));
        lemma_merge_seq_len(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
    }
}

pub open spec fn seq_count(s: Seq<int>, v: int) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s.last() == v { 1int } else { 0int }) + seq_count(s.drop_last(), v)
    }
}

proof fn lemma_seq_count_nonneg(s: Seq<int>, v: int)
    ensures seq_count(s, v) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_seq_count_nonneg(s.drop_last(), v);
    }
}

proof fn lemma_seq_count_cons(x: int, rest: Seq<int>, v: int)
    ensures seq_count(seq![x] + rest, v) == seq_count(rest, v) + (if x == v { 1int } else { 0int }),
    decreases rest.len(),
{
    if rest.len() == 0 {
        assert(seq![x] + rest =~= seq![x]);
        assert(seq_count(seq![x] + rest, v) == seq_count(seq![x], v));
        assert(seq![x].drop_last() =~= Seq::<int>::empty());
        assert(seq_count(seq![x], v) == (if x == v { 1int } else { 0int }) + seq_count(seq![x].drop_last(), v));
    } else {
        assert((seq![x] + rest).drop_last() =~= seq![x] + rest.drop_last());
        assert((seq![x] + rest).last() == rest.last());
        lemma_seq_count_cons(x, rest.drop_last(), v);
    }
}

proof fn lemma_seq_count_concat(a: Seq<int>, b: Seq<int>, v: int)
    ensures seq_count(a + b, v) == seq_count(a, v) + seq_count(b, v),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_seq_count_concat(a, b.drop_last(), v);
    }
}

proof fn lemma_seq_count_zero_no_contains(s: Seq<int>, v: int)
    requires !s.contains(v),
    ensures seq_count(s, v) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s.contains(s.last()));
        assert forall |i: int| 0 <= i < s.drop_last().len() implies s.drop_last()[i] == s[i] by {}
        if s.drop_last().contains(v) {
            let idx = choose |idx: int| 0 <= idx < s.drop_last().len() && s.drop_last()[idx] == v;
            assert(s[idx] == v);
            assert(false);
        }
        lemma_seq_count_zero_no_contains(s.drop_last(), v);
    }
}

proof fn lemma_merge_seq_count(a: Seq<int>, b: Seq<int>, v: int)
    ensures seq_count(merge_seq(a, b), v) == seq_count(a, v) + seq_count(b, v),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        assert(merge_seq(a, b) =~= b);
        assert(seq_count(a, v) == 0);
    } else if b.len() == 0 {
        assert(merge_seq(a, b) =~= a);
        assert(seq_count(b, v) == 0);
    } else if a[0] <= b[0] {
        lemma_merge_seq_count(a.drop_first(), b, v);
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
        lemma_seq_count_cons(a[0], merge_seq(a.drop_first(), b), v);
        assert(a =~= seq![a[0]] + a.drop_first());
        lemma_seq_count_cons(a[0], a.drop_first(), v);
    } else {
        lemma_merge_seq_count(a, b.drop_first(), v);
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
        lemma_seq_count_cons(b[0], merge_seq(a, b.drop_first()), v);
        assert(b =~= seq![b[0]] + b.drop_first());
        lemma_seq_count_cons(b[0], b.drop_first(), v);
    }
}

proof fn lemma_merge_sort_seq_count(s: Seq<int>, v: int)
    ensures seq_count(merge_sort_seq(s), v) == seq_count(s, v),
    decreases s.len(),
{
    if s.len() > 1 {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_count(s.subrange(0, mid), v);
        lemma_merge_sort_seq_count(s.subrange(mid, s.len() as int), v);
        lemma_merge_seq_count(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), v);
        assert(s =~= s.subrange(0, mid) + s.subrange(mid, s.len() as int));
        lemma_seq_count_concat(s.subrange(0, mid), s.subrange(mid, s.len() as int), v);
    }
}

proof fn lemma_merge_seq_contains(a: Seq<int>, b: Seq<int>, v: int)
    ensures merge_seq(a, b).contains(v) <==> (a.contains(v) || b.contains(v)),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        assert(merge_seq(a, b) =~= b);
    } else if b.len() == 0 {
        assert(merge_seq(a, b) =~= a);
    } else if a[0] <= b[0] {
        lemma_merge_seq_contains(a.drop_first(), b, v);
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
        assert(a =~= seq![a[0]] + a.drop_first());
        vstd::seq_lib::lemma_seq_concat_contains_all_elements(seq![a[0]], merge_seq(a.drop_first(), b), v);
        vstd::seq_lib::lemma_seq_concat_contains_all_elements(seq![a[0]], a.drop_first(), v);
        assert(seq![a[0]][0] == a[0]);
        if seq![a[0]].contains(v) {
            let idx = choose |idx: int| 0 <= idx < seq![a[0]].len() && seq![a[0]][idx] == v;
            assert(idx == 0);
        }
    } else {
        lemma_merge_seq_contains(a, b.drop_first(), v);
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
        vstd::seq_lib::lemma_seq_concat_contains_all_elements(seq![b[0]], merge_seq(a, b.drop_first()), v);
        vstd::seq_lib::lemma_seq_concat_contains_all_elements(seq![b[0]], b.drop_first(), v);
        assert(seq![b[0]][0] == b[0]);
        if seq![b[0]].contains(v) {
            let idx = choose |idx: int| 0 <= idx < seq![b[0]].len() && seq![b[0]][idx] == v;
            assert(idx == 0);
        }
        assert(b =~= seq![b[0]] + b.drop_first());
    }
}

pub open spec fn pts_encoded(xs: Seq<i32>) -> Seq<int>
    decreases xs.len()
{
    if xs.len() == 0 {
        Seq::empty()
    } else {
        pts_encoded(xs.subrange(0, xs.len() - 1)).push(encode(xs[xs.len() - 1] as int, xs.len() - 1))
    }
}

proof fn lemma_pts_encoded_len(xs: Seq<i32>)
    ensures pts_encoded(xs).len() == xs.len(),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_pts_encoded_len(xs.subrange(0, xs.len() - 1));
    }
}

proof fn lemma_pts_encoded_index(xs: Seq<i32>, i: int)
    requires 0 <= i < xs.len(),
    ensures pts_encoded(xs)[i] == encode(xs[i] as int, i),
    decreases xs.len(),
{
    lemma_pts_encoded_len(xs);
    if i < xs.len() - 1 {
        lemma_pts_encoded_index(xs.subrange(0, xs.len() - 1), i);
        assert(xs.subrange(0, xs.len() - 1)[i] == xs[i]);
    }
}

proof fn lemma_pts_encoded_count_le1(xs: Seq<i32>, v: int)
    requires xs.len() <= 200000,
    ensures seq_count(pts_encoded(xs), v) <= 1,
    decreases xs.len(),
{
    lemma_pts_encoded_len(xs);
    if xs.len() > 0 {
        let prev = xs.subrange(0, xs.len() - 1);
        lemma_pts_encoded_count_le1(prev, v);
        let lastidx = xs.len() - 1;
        let lastenc = encode(xs[lastidx] as int, lastidx);
        assert(pts_encoded(xs) =~= pts_encoded(prev).push(lastenc));
        assert(pts_encoded(xs).drop_last() =~= pts_encoded(prev));
        assert(pts_encoded(xs).last() == lastenc);
        if lastenc == v {
            if pts_encoded(prev).contains(v) {
                lemma_pts_encoded_len(prev);
                let i = choose |i: int| 0 <= i < prev.len() && pts_encoded(prev)[i] == v;
                lemma_pts_encoded_index(prev, i);
                assert(prev[i] == xs[i]);
                assert(encode(xs[i] as int, i) == v);
                assert(v == lastenc);
                assert(encode(xs[i] as int, i) == encode(xs[lastidx] as int, lastidx));
                lemma_encode_order(xs[i] as int, i, xs[lastidx] as int, lastidx);
                assert(i == lastidx);
                assert(false);
            }
            lemma_seq_count_zero_no_contains(pts_encoded(prev), v);
        }
    }
}

pub open spec fn sorted_enc(xs: Seq<i32>) -> Seq<int> {
    merge_sort_seq(pts_encoded(xs))
}

proof fn lemma_merge_sort_seq_contains(s: Seq<int>, v: int)
    ensures merge_sort_seq(s).contains(v) <==> s.contains(v),
    decreases s.len(),
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_contains(s.subrange(0, mid), v);
        lemma_merge_sort_seq_contains(s.subrange(mid, s.len() as int), v);
        lemma_merge_seq_contains(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), v);
        assert(s =~= s.subrange(0, mid) + s.subrange(mid, s.len() as int));
        assert forall |x: int| s.contains(x) implies (s.subrange(0, mid).contains(x) || s.subrange(mid, s.len() as int).contains(x)) by {
            if s.contains(x) {
                let k = choose |k: int| 0 <= k < s.len() && s[k] == x;
                if k < mid {
                    assert(s.subrange(0, mid)[k] == x);
                } else {
                    assert(s.subrange(mid, s.len() as int)[k - mid] == x);
                }
            }
        }
        assert forall |x: int| (s.subrange(0, mid).contains(x) || s.subrange(mid, s.len() as int).contains(x)) implies s.contains(x) by {
            if s.subrange(0, mid).contains(x) {
                let k = choose |k: int| 0 <= k < mid && s.subrange(0, mid)[k] == x;
                assert(s[k] == x);
            }
            if s.subrange(mid, s.len() as int).contains(x) {
                let k = choose |k: int| 0 <= k < s.len() - mid && s.subrange(mid, s.len() as int)[k] == x;
                assert(s[k + mid] == x);
            }
        }
    }
}

proof fn lemma_sorted_enc_props(xs: Seq<i32>)
    requires xs.len() <= 200000,
    ensures
        sorted_asc(sorted_enc(xs)),
        sorted_enc(xs).len() == xs.len(),
        forall |v: int| sorted_enc(xs).contains(v) <==> pts_encoded(xs).contains(v),
        forall |v: int| seq_count(sorted_enc(xs), v) <= 1,
{
    lemma_merge_sort_seq_sorted(pts_encoded(xs));
    lemma_merge_sort_seq_len(pts_encoded(xs));
    lemma_pts_encoded_len(xs);
    assert forall |v: int| sorted_enc(xs).contains(v) <==> pts_encoded(xs).contains(v) by {
        lemma_merge_sort_seq_contains(pts_encoded(xs), v);
    }
    assert forall |v: int| seq_count(sorted_enc(xs), v) <= 1 by {
        lemma_merge_sort_seq_count(pts_encoded(xs), v);
        lemma_pts_encoded_count_le1(xs, v);
    }
}

proof fn lemma_sorted_enc_pos_to_index(xs: Seq<i32>, p: int)
    requires
        0 <= p < xs.len(),
        xs.len() <= 200000,
    ensures
        0 <= decode_idx(sorted_enc(xs)[p]) < xs.len(),
        sorted_enc(xs)[p] == encode(xs[decode_idx(sorted_enc(xs)[p])] as int, decode_idx(sorted_enc(xs)[p])),
{
    lemma_sorted_enc_props(xs);
    assert(sorted_enc(xs).contains(sorted_enc(xs)[p]));
    assert(pts_encoded(xs).contains(sorted_enc(xs)[p]));
    lemma_pts_encoded_len(xs);
    let i = choose |i: int| 0 <= i < xs.len() && pts_encoded(xs)[i] == sorted_enc(xs)[p];
    lemma_pts_encoded_index(xs, i);
    assert(sorted_enc(xs)[p] == encode(xs[i] as int, i));
    lemma_encode_decode_idx(xs[i] as int, i);
    assert(decode_idx(sorted_enc(xs)[p]) == i);
}

proof fn lemma_two_distinct_positions_count_ge2(s: Seq<int>, p1: int, p2: int, v: int)
    requires
        0 <= p1 < s.len(), 0 <= p2 < s.len(), p1 != p2,
        s[p1] == v, s[p2] == v,
    ensures seq_count(s, v) >= 2,
    decreases s.len(),
{
    lemma_seq_count_nonneg(s, v);
    let lo = if p1 < p2 { p1 } else { p2 };
    let hi = if p1 < p2 { p2 } else { p1 };
    assert(0 <= lo < hi < s.len());
    assert(s[lo] == v);
    assert(s[hi] == v);
    if hi == s.len() - 1 {
        assert(s.last() == v);
        assert(s.drop_last()[lo] == v);
        assert(0 <= lo < s.drop_last().len());
        lemma_seq_count_contains_ge1(s.drop_last(), v, lo);
        assert(seq_count(s, v) == 1 + seq_count(s.drop_last(), v));
    } else {
        lemma_two_distinct_positions_count_ge2(s.drop_last(), p1, p2, v);
    }
}

proof fn lemma_seq_count_contains_ge1(s: Seq<int>, v: int, idx: int)
    requires 0 <= idx < s.len(), s[idx] == v,
    ensures seq_count(s, v) >= 1,
    decreases s.len(),
{
    lemma_seq_count_nonneg(s, v);
    if idx == s.len() - 1 {
        assert(s.last() == v);
        lemma_seq_count_nonneg(s.drop_last(), v);
    } else {
        assert(s.drop_last()[idx] == v);
        lemma_seq_count_contains_ge1(s.drop_last(), v, idx);
    }
}

proof fn lemma_sorted_enc_injective(xs: Seq<i32>, p1: int, p2: int)
    requires
        0 <= p1 < xs.len(), 0 <= p2 < xs.len(), p1 != p2,
        xs.len() <= 200000,
    ensures decode_idx(sorted_enc(xs)[p1]) != decode_idx(sorted_enc(xs)[p2]),
{
    lemma_sorted_enc_props(xs);
    lemma_sorted_enc_pos_to_index(xs, p1);
    lemma_sorted_enc_pos_to_index(xs, p2);
    if decode_idx(sorted_enc(xs)[p1]) == decode_idx(sorted_enc(xs)[p2]) {
        assert(sorted_enc(xs)[p1] == sorted_enc(xs)[p2]);
        let v = sorted_enc(xs)[p1];
        lemma_two_distinct_positions_count_ge2(sorted_enc(xs), p1, p2, v);
        assert(seq_count(sorted_enc(xs), v) >= 2);
        assert(false);
    }
}

pub open spec fn to_int_seq64(s: Seq<i64>) -> Seq<int> {
    s.map_values(|x: i64| x as int)
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

fn merge_exec(a: &Vec<i64>, b: &Vec<i64>) -> (result: Vec<i64>)
    requires
        sorted_asc(to_int_seq64(a@)),
        sorted_asc(to_int_seq64(b@)),
    ensures
        to_int_seq64(result@) == merge_seq(to_int_seq64(a@), to_int_seq64(b@)),
{
    let ghost av = to_int_seq64(a@);
    let ghost bv = to_int_seq64(b@);
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(av.skip(0) =~= av);
        assert(bv.skip(0) =~= bv);
        assert(to_int_seq64(result@) =~= Seq::<int>::empty());
    }
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j,
            to_int_seq64(a@) == av,
            to_int_seq64(b@) == bv,
            to_int_seq64(result@) + merge_seq(av.skip(i as int), bv.skip(j as int)) == merge_seq(av, bv),
        decreases (a.len() - i) + (b.len() - j),
    {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            proof {
                lemma_merge_seq_skip_step_a(av, bv, i as int, j as int);
                assert(to_int_seq64(result@).push(a@[i as int] as int) =~= to_int_seq64(result@) + seq![a@[i as int] as int]);
            }
            result.push(a[i]);
            i += 1;
        } else {
            proof {
                lemma_merge_seq_skip_step_b(av, bv, i as int, j as int);
                assert(to_int_seq64(result@).push(b@[j as int] as int) =~= to_int_seq64(result@) + seq![b@[j as int] as int]);
            }
            result.push(b[j]);
            j += 1;
        }
    }
    proof {
        assert(av.skip(i as int).len() == 0);
        assert(bv.skip(j as int).len() == 0);
        assert(merge_seq(av.skip(i as int), bv.skip(j as int)) =~= Seq::<int>::empty());
        assert(to_int_seq64(result@) == merge_seq(av, bv));
    }
    result
}

fn merge_sort_exec(v: &Vec<i64>) -> (result: Vec<i64>)
    requires v.len() <= 200_000,
    ensures to_int_seq64(result@) == merge_sort_seq(to_int_seq64(v@)),
    decreases v.len()
{
    if v.len() <= 1 {
        let mut result: Vec<i64> = Vec::new();
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
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant i <= mid, mid <= v.len(), left@.len() == i as int,
                forall |t: int| 0 <= t < i ==> left@[t] == v@[t],
            decreases mid - i,
        {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i64> = Vec::new();
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
            lemma_merge_sort_seq_sorted(to_int_seq64(v@).subrange(0, mid as int));
            lemma_merge_sort_seq_sorted(to_int_seq64(v@).subrange(mid as int, v@.len() as int));
            assert(to_int_seq64(left@) =~= to_int_seq64(v@).subrange(0, mid as int));
            assert(to_int_seq64(right@) =~= to_int_seq64(v@).subrange(mid as int, v@.len() as int));
        }
        let result = merge_exec(&sorted_left, &sorted_right);
        proof {
            assert(to_int_seq64(result@) == merge_seq(to_int_seq64(sorted_left@), to_int_seq64(sorted_right@)));
            assert(merge_sort_seq(to_int_seq64(v@)) ==
                merge_seq(merge_sort_seq(to_int_seq64(v@).subrange(0, mid as int)),
                    merge_sort_seq(to_int_seq64(v@).subrange(mid as int, v@.len() as int))));
        }
        result
    }
}

fn encode_exec(v: i32, i: usize) -> (result: i64)
    requires 0 <= v <= 1_000_000_000, i < 100000,
    ensures result as int == encode(v as int, i as int),
{
    (v as i64) * 200000 + (i as i64)
}

fn decode_val_exec(e: i64) -> (result: i64)
    requires 0 <= e <= 1_000_000_000i64 * 200000i64 + 99999i64,
    ensures result as int == decode_val(e as int),
{
    e / 200000
}

impl Solution {
    pub fn min_rectangles_to_cover_points(points: Vec<Vec<i32>>, w: i32) -> (result: i32)
        requires
            1 <= points.len() <= 100000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 1000000000,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][1] <= 1000000000,
            0 <= w <= 1000000000,
            forall |i: int, j: int| 0 <= i < j < points.len() ==> #[trigger] points[i] != #[trigger] points[j],
        ensures
            exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, Self::x_seq(points@))
                && result as int == Self::min_rectangles_sorted_from(s, w as int, 0),
    {
        let n = points.len();
        let mut xs: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100000,
                n == points.len(),
                0 <= i <= n,
                forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t].len() == 2,
                forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][0] <= 1000000000,
                xs.len() == i,
                xs@ == Self::x_prefix(points@, i as int),
                forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
            decreases n - i,
        {
            proof {
                assert(points[i as int].len() == 2);
            }
            let ghost old_xs_seq = xs@;
            xs.push(points[i][0]);
            proof {
                assert(xs@ == old_xs_seq.push(points[i as int][0]));
                assert(old_xs_seq == Self::x_prefix(points@, i as int));
                assert(Self::x_prefix(points@, i as int + 1)
                    == Self::x_prefix(points@, i as int).push(points[i as int][0]));
                assert(xs@ == Self::x_prefix(points@, i as int + 1));
            }
            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(xs@ == Self::x_prefix(points@, n as int));
            assert(n as int == points@.len());
            assert(Self::x_seq(points@) == Self::x_prefix(points@, n as int));
            assert(xs@ == Self::x_seq(points@));
        }

        let ghost old_xs = xs@;

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n
            invariant
                ii <= n,
                n == xs.len(),
                n <= 100000,
                enc.len() == ii,
                forall |t: int| 0 <= t < n as int ==> 0 <= #[trigger] xs@[t] <= 1_000_000_000,
                forall |t: int| 0 <= t < ii as int ==> enc@[t] as int == encode(xs@[t] as int, t),
            decreases n - ii,
        {
            let e = encode_exec(xs[ii], ii);
            enc.push(e);
            ii += 1;
        }
        proof {
            lemma_pts_encoded_len(xs@);
            assert forall |t: int| 0 <= t < n as int implies enc@[t] as int == pts_encoded(xs@)[t] by {
                lemma_pts_encoded_index(xs@, t);
            }
            assert(to_int_seq64(enc@).len() == pts_encoded(xs@).len());
            assert(to_int_seq64(enc@) =~= pts_encoded(xs@));
        }

        let sorted_codes = merge_sort_exec(&enc);
        proof {
            assert(to_int_seq64(sorted_codes@) == merge_sort_seq(pts_encoded(xs@)));
            assert(to_int_seq64(sorted_codes@) == sorted_enc(xs@));
            lemma_sorted_enc_props(xs@);
        }

        let mut sorted_xs: Vec<i32> = Vec::new();
        let mut pp: usize = 0;
        while pp < n
            invariant
                pp <= n,
                n == xs.len(),
                n <= 100000,
                sorted_codes.len() == n,
                to_int_seq64(sorted_codes@) == sorted_enc(xs@),
                forall |t: int| 0 <= t < n as int ==> 0 <= #[trigger] xs@[t] <= 1_000_000_000,
                sorted_xs.len() == pp,
                forall |t: int| 0 <= t < pp as int ==> sorted_xs@[t] as int == decode_val(sorted_enc(xs@)[t]),
                forall |t: int| 0 <= t < pp as int ==> sorted_xs@[t] as int == xs@[decode_idx(sorted_enc(xs@)[t])] as int,
            decreases n - pp,
        {
            proof {
                assert(sorted_codes@[pp as int] as int == sorted_enc(xs@)[pp as int]);
                assert(0 <= sorted_enc(xs@)[pp as int] <= 1_000_000_000i64 as int * 200000i64 as int + 99999i64 as int) by {
                    lemma_sorted_enc_pos_to_index(xs@, pp as int);
                    let idx = decode_idx(sorted_enc(xs@)[pp as int]);
                    assert(sorted_enc(xs@)[pp as int] == encode(xs@[idx] as int, idx));
                    assert(0 <= xs@[idx] <= 1000000000);
                    assert(0 <= idx < n as int);
                };
            }
            let dv = decode_val_exec(sorted_codes[pp]);
            proof {
                lemma_sorted_enc_pos_to_index(xs@, pp as int);
                let idx = decode_idx(sorted_enc(xs@)[pp as int]);
                assert(sorted_enc(xs@)[pp as int] == encode(xs@[idx] as int, idx));
                lemma_encode_decode_val(xs@[idx] as int, idx);
                assert(dv as int == xs@[idx] as int);
                assert(0 <= dv as int <= 1000000000);
            }
            let v32 = dv as i32;
            sorted_xs.push(v32);
            proof {
                assert(sorted_xs@[pp as int] as int == v32 as int);
                assert(sorted_xs@[pp as int] as int == decode_val(sorted_enc(xs@)[pp as int]));
                let idx = decode_idx(sorted_enc(xs@)[pp as int]);
                assert(sorted_xs@[pp as int] as int == xs@[idx] as int);
            }
            pp += 1;
        }

        proof {
            assert(sorted_xs@.len() == n as int);
            assert forall |i1: int, j1: int| 0 <= i1 < j1 < n as int implies sorted_xs@[i1] <= sorted_xs@[j1] by {
                assert(sorted_enc(xs@)[i1] <= sorted_enc(xs@)[j1]);
                let idx_i = decode_idx(sorted_enc(xs@)[i1]);
                let idx_j = decode_idx(sorted_enc(xs@)[j1]);
                lemma_sorted_enc_pos_to_index(xs@, i1);
                lemma_sorted_enc_pos_to_index(xs@, j1);
                assert(sorted_enc(xs@)[i1] == encode(xs@[idx_i] as int, idx_i));
                assert(sorted_enc(xs@)[j1] == encode(xs@[idx_j] as int, idx_j));
                if xs@[idx_i] as int > xs@[idx_j] as int {
                    lemma_encode_order(xs@[idx_i] as int, idx_i, xs@[idx_j] as int, idx_j);
                    assert(encode(xs@[idx_i] as int, idx_i) > encode(xs@[idx_j] as int, idx_j));
                    assert(false);
                }
                assert(sorted_xs@[i1] as int == xs@[idx_i] as int);
                assert(sorted_xs@[j1] as int == xs@[idx_j] as int);
            }
            assert(Self::sorted_between(sorted_xs@, 0, sorted_xs@.len() as int));

            let r = Seq::new(n as nat, |p: int| decode_idx(sorted_enc(xs@)[p]));
            assert forall |p: int| 0 <= p < r.len() implies 0 <= #[trigger] r[p] < r.len() by {
                lemma_sorted_enc_pos_to_index(xs@, p);
            }
            assert forall |i1: int, j1: int| 0 <= i1 < j1 < r.len() implies r[i1] != r[j1] by {
                lemma_sorted_enc_injective(xs@, i1, j1);
            }
            assert forall |p: int| 0 <= p < n as int implies #[trigger] sorted_xs@[p] == r.map_values(|i: int| xs@[i])[p] by {
                assert(r.map_values(|i: int| xs@[i])[p] == xs@[r[p]]);
                assert(r[p] == decode_idx(sorted_enc(xs@)[p]));
            }
            assert(sorted_xs@ =~= r.map_values(|i: int| xs@[i]));
            assert(Self::is_reorder_of(r, sorted_xs@, xs@));
            assert(xs@ == old_xs);
            assert(old_xs == Self::x_seq(points@));
        }

        let xs = sorted_xs;

        let mut ans: i32 = 0;
        let mut p: usize = 0;
        while p < n
            invariant
                1 <= n <= 100000,
                n == xs.len(),
                old_xs.len() == n as int,
                0 <= w <= 1000000000,
                0 <= p <= n,
                0 <= ans as int <= p as int,
                forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
                Self::sorted_between(xs@, 0, n as int),
                exists|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs),
                ans as int + Self::min_rectangles_sorted_from(xs@, w as int, p as int)
                    == Self::min_rectangles_sorted_from(xs@, w as int, 0),
            decreases n - p,
        {
            let ghost old_p = p as int;
            let ghost old_ans = ans as int;
            proof {
                assert(old_p < n as int);
                assert(0 <= xs[old_p] as int <= 1000000000);
                assert(0 <= w as int <= 1000000000);
                assert(xs[old_p] as int + w as int <= 2000000000);
            }
            let cover = xs[p] + w;
            p = p + 1;
            while p < n && xs[p] <= cover
                invariant
                    1 <= n <= 100000,
                    n == xs.len(),
                    old_xs.len() == n as int,
                    0 <= w <= 1000000000,
                    old_p < n as int,
                    old_ans + Self::min_rectangles_sorted_from(xs@, w as int, old_p)
                        == Self::min_rectangles_sorted_from(xs@, w as int, 0),
                    old_ans <= old_p,
                    old_p + 1 <= p as int <= n as int,
                    cover as int == xs[old_p] as int + w as int,
                    forall |t: int| old_p + 1 <= t < p as int ==> xs[t] as int <= cover as int,
                    forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
                    Self::sorted_between(xs@, 0, n as int),
                    exists|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs),
                decreases n - p,
            {
                p = p + 1;
            }

            proof {
                if p < n {
                    assert(!(xs[p as int] <= cover));
                    assert(xs[p as int] as int > cover as int);
                }
                Self::lemma_continue_skip_prefix(xs@, w as int, old_p + 1, cover as int, p as int);
                assert(Self::min_rectangles_continue(xs@, w as int, old_p + 1, cover as int)
                    == Self::min_rectangles_continue(xs@, w as int, p as int, cover as int));
                if p < n {
                    Self::lemma_continue_at_gt_equals_sorted(xs@, w as int, p as int, cover as int);
                    assert(Self::min_rectangles_continue(xs@, w as int, p as int, cover as int)
                        == Self::min_rectangles_sorted_from(xs@, w as int, p as int));
                } else {
                    assert(p as int == n as int);
                    assert(Self::min_rectangles_continue(xs@, w as int, p as int, cover as int) == 0);
                    assert(Self::min_rectangles_sorted_from(xs@, w as int, p as int) == 0);
                }
                assert(Self::min_rectangles_sorted_from(xs@, w as int, old_p)
                    == 1 + Self::min_rectangles_sorted_from(xs@, w as int, p as int));
            }

            ans = ans + 1;
            proof {
                assert(ans as int == old_ans + 1);
                assert(ans as int + Self::min_rectangles_sorted_from(xs@, w as int, p as int)
                    == Self::min_rectangles_sorted_from(xs@, w as int, 0));
                assert(old_ans <= old_p);
                assert(old_p + 1 <= p as int);
                assert(ans as int <= p as int);
            }
        }

        proof {
            assert(p == n);
            assert(Self::min_rectangles_sorted_from(xs@, w as int, n as int) == 0);
            assert(ans as int == Self::min_rectangles_sorted_from(xs@, w as int, 0));
            assert(old_xs == Self::x_seq(points@));

            let r_final = choose|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs);
            assert(exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, Self::x_seq(points@))
                && ans as int == Self::min_rectangles_sorted_from(s, w as int, 0)) by {
                let s = xs@;
                let r = r_final;
                assert(Self::sorted_between(s, 0, s.len() as int));
                assert(Self::is_reorder_of(r, s, Self::x_seq(points@)));
                assert(ans as int == Self::min_rectangles_sorted_from(s, w as int, 0));
            };
        }

        ans
    }
}

}
