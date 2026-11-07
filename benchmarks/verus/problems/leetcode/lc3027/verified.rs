use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_concat_contains_all_elements;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_bound, lemma_fundamental_div_mod_converse};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inside(points: Seq<Seq<int>>, i: int, j: int, t: int) -> bool {
        &&& points[i][0] <= points[t][0]
        &&& points[t][0] <= points[j][0]
        &&& points[j][1] <= points[t][1]
        &&& points[t][1] <= points[i][1]
    }

    pub open spec fn valid_pair(points: Seq<Seq<int>>, i: int, j: int) -> bool {
        &&& i != j
        &&& points[i][0] <= points[j][0]
        &&& points[i][1] >= points[j][1]
        &&& (forall|t: int|
            0 <= t < points.len() && t != i && t != j ==> !Self::inside(points, i, j, t))
    }

    pub open spec fn count_j(points: Seq<Seq<int>>, i: int, jend: int) -> int
        decreases jend,
    {
        if jend <= 0 {
            0
        } else {
            Self::count_j(points, i, jend - 1) + (if Self::valid_pair(points, i, jend - 1) {
                1int
            } else {
                0int
            })
        }
    }

    pub open spec fn count_i(points: Seq<Seq<int>>, iend: int) -> int
        decreases iend,
    {
        if iend <= 0 {
            0
        } else {
            Self::count_i(points, iend - 1) + Self::count_j(points, iend - 1, points.len() as int)
        }
    }

    pub open spec fn spec_number_of_pairs(points: Seq<Seq<int>>) -> int {
        Self::count_i(points, points.len() as int)
    }
}

proof fn lemma_count_j_step(points: Seq<Seq<int>>, i: int, jend: int)
    requires 0 <= jend < points.len(),
    ensures Solution::count_j(points, i, jend + 1)
        == Solution::count_j(points, i, jend) + if Solution::valid_pair(points, i, jend) { 1int } else { 0int },
{
}

proof fn lemma_count_j_bound(points: Seq<Seq<int>>, i: int, jend: int)
    requires 0 <= jend <= points.len(),
    ensures 0 <= Solution::count_j(points, i, jend) <= jend,
    decreases jend
{
    if jend > 0 {
        lemma_count_j_bound(points, i, jend - 1);
    }
}

proof fn lemma_count_i_bound(points: Seq<Seq<int>>, iend: int)
    requires 0 <= iend <= points.len(),
    ensures 0 <= Solution::count_i(points, iend) <= iend * points.len(),
    decreases iend
{
    if iend > 0 {
        lemma_count_i_bound(points, iend - 1);
        lemma_count_j_bound(points, iend - 1, points.len() as int);
        assert((iend - 1) * points.len() + points.len() == iend * points.len()) by (nonlinear_arith);
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

pub open spec fn all_ge(s: Seq<int>, lo: int) -> bool {
    forall|k: int| 0 <= k < s.len() ==> s[k] >= lo
}

proof fn lemma_sorted_drop_first(s: Seq<int>)
    requires sorted_asc(s), s.len() > 0,
    ensures sorted_asc(s.drop_first()), all_ge(s.drop_first(), s[0]),
{
    assert forall|a: int, b: int| 0 <= a <= b < s.drop_first().len() implies
        s.drop_first()[a] <= s.drop_first()[b] by {
        assert(s.drop_first()[a] == s[a + 1]);
        assert(s.drop_first()[b] == s[b + 1]);
    }
    assert forall|k: int| 0 <= k < s.drop_first().len() implies s.drop_first()[k] >= s[0] by {
        assert(s.drop_first()[k] == s[k + 1]);
    }
}

proof fn lemma_sorted_cons(x: int, rest: Seq<int>)
    requires all_ge(rest, x), sorted_asc(rest),
    ensures sorted_asc(seq![x] + rest),
{
    assert forall|a: int, b: int| 0 <= a <= b < (seq![x] + rest).len() implies
        (seq![x] + rest)[a] <= (seq![x] + rest)[b] by {
        if a == 0 {
            if b > 0 {
                assert((seq![x] + rest)[b] == rest[b - 1]);
                assert(rest[b - 1] >= x);
            }
        } else {
            assert((seq![x] + rest)[a] == rest[a - 1]);
            assert((seq![x] + rest)[b] == rest[b - 1]);
        }
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

pub open spec fn encode(x: int, y: int) -> int {
    (x + 1_000_000_000) * 2_000_000_003 + (1_000_000_000 - y)
}

pub open spec fn decode_x(e: int) -> int {
    e / 2_000_000_003 - 1_000_000_000
}

pub open spec fn decode_y(e: int) -> int {
    1_000_000_000 - (e % 2_000_000_003)
}

proof fn lemma_encode_decode(x: int, y: int)
    requires -1_000_000_000 <= x <= 1_000_000_000, -1_000_000_000 <= y <= 1_000_000_000,
    ensures decode_x(encode(x, y)) == x, decode_y(encode(x, y)) == y,
{
    let q = x + 1_000_000_000;
    let r = 1_000_000_000 - y;
    assert(0 <= r < 2_000_000_003);
    assert(encode(x, y) == q * 2_000_000_003 + r);
    lemma_fundamental_div_mod_converse(encode(x, y), 2_000_000_003, q, r);
}

proof fn lemma_encode_order(x1: int, y1: int, x2: int, y2: int)
    requires -1_000_000_000 <= x1 <= 1_000_000_000, -1_000_000_000 <= y1 <= 1_000_000_000,
        -1_000_000_000 <= x2 <= 1_000_000_000, -1_000_000_000 <= y2 <= 1_000_000_000,
    ensures encode(x1, y1) < encode(x2, y2) <==> (x1 < x2 || (x1 == x2 && y1 > y2)),
        encode(x1, y1) == encode(x2, y2) <==> (x1 == x2 && y1 == y2),
{
    lemma_encode_decode(x1, y1);
    lemma_encode_decode(x2, y2);
}

pub open spec fn valid_enc(e: int) -> bool {
    &&& -1_000_000_000 <= decode_x(e) <= 1_000_000_000
    &&& -1_000_000_000 <= decode_y(e) <= 1_000_000_000
    &&& e == encode(decode_x(e), decode_y(e))
}

proof fn lemma_valid_enc_of_encode(x: int, y: int)
    requires -1_000_000_000 <= x <= 1_000_000_000, -1_000_000_000 <= y <= 1_000_000_000,
    ensures valid_enc(encode(x, y)), decode_x(encode(x, y)) == x, decode_y(encode(x, y)) == y,
{
    lemma_encode_decode(x, y);
}

proof fn lemma_decode_order(e1: int, e2: int)
    requires valid_enc(e1), valid_enc(e2),
    ensures
        e1 < e2 <==> (decode_x(e1) < decode_x(e2) || (decode_x(e1) == decode_x(e2) && decode_y(e1) > decode_y(e2))),
        e1 == e2 <==> (decode_x(e1) == decode_x(e2) && decode_y(e1) == decode_y(e2)),
{
    lemma_encode_order(decode_x(e1), decode_y(e1), decode_x(e2), decode_y(e2));
}

pub open spec fn is_candidate(points: Seq<Seq<int>>, i: int, t: int) -> bool {
    &&& t != i
    &&& points[i][0] <= points[t][0]
    &&& points[t][1] <= points[i][1]
}

pub open spec fn is_dominant(points: Seq<Seq<int>>, i: int, j: int) -> bool {
    forall |t: int| 0 <= t < points.len() && t != i && t != j && is_candidate(points, i, t)
        ==> !(points[t][0] <= points[j][0] && points[j][1] <= points[t][1])
}

proof fn lemma_valid_pair_char(points: Seq<Seq<int>>, i: int, j: int)
    requires 0 <= i < points.len(), 0 <= j < points.len(), i != j,
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
    ensures Solution::valid_pair(points, i, j) <==> (
        is_candidate(points, i, j) && is_dominant(points, i, j)
    ),
{
    assert forall |t: int| 0 <= t < points.len() && t != i && t != j implies
        (!Solution::inside(points, i, j, t) <==> (is_candidate(points, i, t)
            ==> !(points[t][0] <= points[j][0] && points[j][1] <= points[t][1]))) by {
        if is_candidate(points, i, t) {
        } else {
            assert(!(points[i][0] <= points[t][0] && points[t][1] <= points[i][1]));
        }
    }
    if Solution::valid_pair(points, i, j) {
        assert(is_candidate(points, i, j));
        assert forall |t: int| 0 <= t < points.len() && t != i && t != j && is_candidate(points, i, t)
            implies !(points[t][0] <= points[j][0] && points[j][1] <= points[t][1]) by {
            assert(!Solution::inside(points, i, j, t));
        }
        assert(is_dominant(points, i, j));
    }
    if is_candidate(points, i, j) && is_dominant(points, i, j) {
        assert forall |t: int| 0 <= t < points.len() && t != i && t != j implies
            !Solution::inside(points, i, j, t) by {
            if is_candidate(points, i, t) {
                assert(!(points[t][0] <= points[j][0] && points[j][1] <= points[t][1]));
            }
        }
        assert(Solution::valid_pair(points, i, j));
    }
}

pub open spec fn count_dominant_upto(points: Seq<Seq<int>>, i: int, jend: int) -> int
    decreases jend
{
    if jend <= 0 {
        0
    } else {
        count_dominant_upto(points, i, jend - 1)
            + if is_candidate(points, i, jend - 1) && is_dominant(points, i, jend - 1) { 1int } else { 0int }
    }
}

proof fn lemma_count_j_eq_count_dominant(points: Seq<Seq<int>>, i: int, jend: int)
    requires 0 <= i < points.len(), 0 <= jend <= points.len(),
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
    ensures Solution::count_j(points, i, jend) == count_dominant_upto(points, i, jend),
    decreases jend
{
    if jend > 0 {
        lemma_count_j_eq_count_dominant(points, i, jend - 1);
        if jend - 1 != i {
            lemma_valid_pair_char(points, i, jend - 1);
        }
    }
}

pub open spec fn candidates_upto(points: Seq<Seq<int>>, i: int, jend: int) -> Seq<int>
    decreases jend
{
    if jend <= 0 {
        Seq::<int>::empty()
    } else {
        let rest = candidates_upto(points, i, jend - 1);
        if is_candidate(points, i, jend - 1) {
            rest.push(encode(points[jend - 1][0], points[jend - 1][1]))
        } else {
            rest
        }
    }
}

pub open spec fn max_y_prefix(s: Seq<int>, idx: int) -> int
    decreases idx
{
    if idx <= 0 {
        -2_000_000_001
    } else {
        let prev = max_y_prefix(s, idx - 1);
        let y = decode_y(s[idx - 1]);
        if y > prev { y } else { prev }
    }
}

pub open spec fn sweep_count(s: Seq<int>, idx: int) -> int
    decreases idx
{
    if idx <= 0 {
        0
    } else {
        sweep_count(s, idx - 1) + if decode_y(s[idx - 1]) > max_y_prefix(s, idx - 1)
            && (idx == s.len() || s[idx] != s[idx - 1]) { 1int } else { 0int }
    }
}

pub open spec fn count_pred(s: Seq<int>, pred: spec_fn(int) -> bool) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if pred(s[0]) { 1int } else { 0int }) + count_pred(s.drop_first(), pred)
    }
}

proof fn lemma_count_pred_cons(x: int, rest: Seq<int>, pred: spec_fn(int) -> bool)
    ensures count_pred(seq![x] + rest, pred) == (if pred(x) { 1int } else { 0int }) + count_pred(rest, pred),
{
    assert((seq![x] + rest).drop_first() =~= rest);
    assert((seq![x] + rest)[0] == x);
}

proof fn lemma_merge_seq_count_pred(a: Seq<int>, b: Seq<int>, pred: spec_fn(int) -> bool)
    ensures count_pred(merge_seq(a, b), pred) == count_pred(a, pred) + count_pred(b, pred),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_count_pred(a.drop_first(), b, pred);
        lemma_count_pred_cons(a[0], merge_seq(a.drop_first(), b), pred);
        lemma_count_pred_cons(a[0], a.drop_first(), pred);
    } else {
        lemma_merge_seq_count_pred(a, b.drop_first(), pred);
        lemma_count_pred_cons(b[0], merge_seq(a, b.drop_first()), pred);
        lemma_count_pred_cons(b[0], b.drop_first(), pred);
    }
}

proof fn lemma_count_pred_split(s: Seq<int>, mid: int, pred: spec_fn(int) -> bool)
    requires 0 <= mid <= s.len(),
    ensures count_pred(s, pred) == count_pred(s.subrange(0, mid), pred) + count_pred(s.subrange(mid, s.len() as int), pred),
    decreases mid
{
    if mid == 0 {
        assert(s.subrange(0, 0) =~= Seq::<int>::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(s.len() > 0);
        lemma_count_pred_split(s.drop_first(), mid - 1, pred);
        assert(s.drop_first().subrange(0, mid - 1) =~= s.subrange(1, mid));
        assert(s.drop_first().subrange(mid - 1, s.drop_first().len() as int) =~= s.subrange(mid, s.len() as int));
        assert(s.subrange(0, mid) =~= seq![s[0]] + s.subrange(1, mid));
        lemma_count_pred_cons(s[0], s.subrange(1, mid), pred);
    }
}

proof fn lemma_merge_sort_seq_count_pred(s: Seq<int>, pred: spec_fn(int) -> bool)
    ensures count_pred(merge_sort_seq(s), pred) == count_pred(s, pred),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_count_pred(s.subrange(0, mid), pred);
        lemma_merge_sort_seq_count_pred(s.subrange(mid, s.len() as int), pred);
        lemma_merge_seq_count_pred(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), pred);
        lemma_count_pred_split(s, mid, pred);
    }
}

pub open spec fn max_y_smaller_encode(points: Seq<Seq<int>>, i: int, e: int, tend: int) -> int
    decreases tend
{
    if tend <= 0 {
        -2_000_000_001
    } else {
        let prev = max_y_smaller_encode(points, i, e, tend - 1);
        if is_candidate(points, i, tend - 1) && encode(points[tend - 1][0], points[tend - 1][1]) < e {
            let y = points[tend - 1][1];
            if y > prev { y } else { prev }
        } else {
            prev
        }
    }
}

proof fn lemma_max_y_smaller_encode_char(points: Seq<Seq<int>>, i: int, e: int, tend: int)
    requires 0 <= tend <= points.len(),
    ensures
        max_y_smaller_encode(points, i, e, tend) != -2_000_000_001 ==> (
            exists |t: int| 0 <= t < tend && is_candidate(points, i, t)
                && encode(points[t][0], points[t][1]) < e
                && points[t][1] == max_y_smaller_encode(points, i, e, tend)
        ),
        forall |t: int| 0 <= t < tend && is_candidate(points, i, t) && encode(points[t][0], points[t][1]) < e
            ==> #[trigger] points[t][1] <= max_y_smaller_encode(points, i, e, tend),
    decreases tend
{
    if tend > 0 {
        lemma_max_y_smaller_encode_char(points, i, e, tend - 1);
    }
}

proof fn lemma_blocks_iff_encode(points: Seq<Seq<int>>, j: int, t: int)
    requires points[j].len() == 2, points[t].len() == 2,
        -1_000_000_000 <= points[j][0] <= 1_000_000_000, -1_000_000_000 <= points[j][1] <= 1_000_000_000,
        -1_000_000_000 <= points[t][0] <= 1_000_000_000, -1_000_000_000 <= points[t][1] <= 1_000_000_000,
    ensures (points[t][0] <= points[j][0] && points[j][1] <= points[t][1]) <==> (
        (encode(points[t][0], points[t][1]) < encode(points[j][0], points[j][1]) && points[t][1] >= points[j][1])
        || encode(points[t][0], points[t][1]) == encode(points[j][0], points[j][1])
    ),
{
    lemma_encode_order(points[t][0], points[t][1], points[j][0], points[j][1]);
}

pub open spec fn count_candidates_with_val(points: Seq<Seq<int>>, i: int, jend: int, v: int) -> int
    decreases jend
{
    if jend <= 0 {
        0
    } else {
        count_candidates_with_val(points, i, jend - 1, v)
            + if is_candidate(points, i, jend - 1)
                && encode(points[jend - 1][0], points[jend - 1][1]) == v { 1int } else { 0int }
    }
}

proof fn lemma_count_candidates_with_val_nonneg(points: Seq<Seq<int>>, i: int, n: int, v: int)
    ensures count_candidates_with_val(points, i, n, v) >= 0,
    decreases n
{
    if n > 0 {
        lemma_count_candidates_with_val_nonneg(points, i, n - 1, v);
    }
}

proof fn lemma_count_candidates_with_val_ge1(points: Seq<Seq<int>>, i: int, n: int, v: int, j: int)
    requires 0 <= j < n, is_candidate(points, i, j), encode(points[j][0], points[j][1]) == v,
    ensures count_candidates_with_val(points, i, n, v) >= 1,
    decreases n
{
    if n - 1 == j {
        lemma_count_candidates_with_val_nonneg(points, i, n - 1, v);
        assert(count_candidates_with_val(points, i, n, v) == count_candidates_with_val(points, i, n - 1, v)
            + (if is_candidate(points, i, n - 1) && encode(points[n - 1][0], points[n - 1][1]) == v
                { 1int } else { 0int }));
    } else {
        lemma_count_candidates_with_val_ge1(points, i, n - 1, v, j);
        assert(count_candidates_with_val(points, i, n, v) == count_candidates_with_val(points, i, n - 1, v)
            + (if is_candidate(points, i, n - 1) && encode(points[n - 1][0], points[n - 1][1]) == v
                { 1int } else { 0int }));
    }
}

proof fn lemma_count_candidates_with_val_two(points: Seq<Seq<int>>, i: int, n: int, v: int, j: int, t: int)
    requires 0 <= j < n, 0 <= t < n, j != t,
        is_candidate(points, i, j), is_candidate(points, i, t),
        encode(points[j][0], points[j][1]) == v, encode(points[t][0], points[t][1]) == v,
    ensures count_candidates_with_val(points, i, n, v) >= 2,
    decreases n
{
    if n - 1 == j {
        lemma_count_candidates_with_val_ge1(points, i, n - 1, v, t);
    } else if n - 1 == t {
        lemma_count_candidates_with_val_ge1(points, i, n - 1, v, j);
    } else {
        lemma_count_candidates_with_val_two(points, i, n - 1, v, j, t);
    }
}

pub open spec fn count_candidates_with_val_excl(points: Seq<Seq<int>>, i: int, jend: int, v: int, excl: int) -> int
    decreases jend
{
    if jend <= 0 {
        0
    } else {
        count_candidates_with_val_excl(points, i, jend - 1, v, excl)
            + if jend - 1 != excl && is_candidate(points, i, jend - 1)
                && encode(points[jend - 1][0], points[jend - 1][1]) == v { 1int } else { 0int }
    }
}

proof fn lemma_count_candidates_with_val_excl_nonneg(points: Seq<Seq<int>>, i: int, jend: int, v: int, excl: int)
    ensures count_candidates_with_val_excl(points, i, jend, v, excl) >= 0,
    decreases jend
{
    if jend > 0 {
        lemma_count_candidates_with_val_excl_nonneg(points, i, jend - 1, v, excl);
    }
}

proof fn lemma_count_candidates_with_val_excl_zero_iff(points: Seq<Seq<int>>, i: int, jend: int, v: int, excl: int)
    ensures count_candidates_with_val_excl(points, i, jend, v, excl) == 0 <==> (
        !(exists |t: int| 0 <= t < jend && t != excl && is_candidate(points, i, t)
            && encode(points[t][0], points[t][1]) == v)
    ),
    decreases jend
{
    if jend > 0 {
        lemma_count_candidates_with_val_excl_zero_iff(points, i, jend - 1, v, excl);
        lemma_count_candidates_with_val_excl_nonneg(points, i, jend - 1, v, excl);
    }
}

proof fn lemma_count_candidates_with_val_excl_out_of_range(points: Seq<Seq<int>>, i: int, jend: int, v: int, excl: int)
    requires excl >= jend || excl < 0,
    ensures count_candidates_with_val_excl(points, i, jend, v, excl) == count_candidates_with_val(points, i, jend, v),
    decreases jend
{
    if jend > 0 {
        lemma_count_candidates_with_val_excl_out_of_range(points, i, jend - 1, v, excl);
    }
}

proof fn lemma_count_candidates_with_val_split_excl(points: Seq<Seq<int>>, i: int, jend: int, v: int, j: int)
    requires 0 <= j < jend,
    ensures count_candidates_with_val(points, i, jend, v)
        == count_candidates_with_val_excl(points, i, jend, v, j)
            + (if is_candidate(points, i, j) && encode(points[j][0], points[j][1]) == v { 1int } else { 0int }),
    decreases jend
{
    if jend - 1 == j {
        lemma_count_candidates_with_val_excl_out_of_range(points, i, jend - 1, v, j);
    } else {
        lemma_count_candidates_with_val_split_excl(points, i, jend - 1, v, j);
    }
}

proof fn lemma_count_eq_val_candidates_upto(points: Seq<Seq<int>>, i: int, jend: int, v: int)
    requires 0 <= i < points.len(), 0 <= jend <= points.len(),
    ensures count_eq_val(candidates_upto(points, i, jend), v) == count_candidates_with_val(points, i, jend, v),
    decreases jend
{
    if jend > 0 {
        lemma_count_eq_val_candidates_upto(points, i, jend - 1, v);
        if is_candidate(points, i, jend - 1) {
            let e = encode(points[jend - 1][0], points[jend - 1][1]);
            assert(candidates_upto(points, i, jend) =~= candidates_upto(points, i, jend - 1).push(e));
            lemma_count_eq_val_push(candidates_upto(points, i, jend - 1), e, v);
        } else {
            assert(candidates_upto(points, i, jend) =~= candidates_upto(points, i, jend - 1));
        }
    }
}

proof fn lemma_is_dominant_char(points: Seq<Seq<int>>, i: int, j: int)
    requires 0 <= i < points.len(), 0 <= j < points.len(), i != j,
        is_candidate(points, i, j),
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
        forall |k: int| 0 <= k < points.len() ==> -1_000_000_000 <= #[trigger] points[k][0] <= 1_000_000_000
            && -1_000_000_000 <= points[k][1] <= 1_000_000_000,
    ensures is_dominant(points, i, j) <==> (
        points[j][1] > max_y_smaller_encode(points, i, encode(points[j][0], points[j][1]), points.len() as int)
        && !(exists |t: int| 0 <= t < points.len() && t != j && is_candidate(points, i, t)
            && encode(points[t][0], points[t][1]) == encode(points[j][0], points[j][1]))
    ),
{
    let ej = encode(points[j][0], points[j][1]);
    let n = points.len() as int;
    lemma_max_y_smaller_encode_char(points, i, ej, n);
    if is_dominant(points, i, j) {
        if max_y_smaller_encode(points, i, ej, n) != -2_000_000_001 {
            let t = choose |t: int| 0 <= t < n && is_candidate(points, i, t)
                && encode(points[t][0], points[t][1]) < ej
                && points[t][1] == max_y_smaller_encode(points, i, ej, n);
            assert(t != j);
            lemma_blocks_iff_encode(points, j, t);
            if points[t][1] >= points[j][1] {
                assert(false);
            }
            assert(points[t][1] < points[j][1]);
            assert(max_y_smaller_encode(points, i, ej, n) < points[j][1]);
        }
        assert(max_y_smaller_encode(points, i, ej, n) < points[j][1]);
        if exists |t: int| 0 <= t < n && t != j && is_candidate(points, i, t)
            && encode(points[t][0], points[t][1]) == ej {
            let t = choose |t: int| 0 <= t < n && t != j && is_candidate(points, i, t)
                && encode(points[t][0], points[t][1]) == ej;
            lemma_blocks_iff_encode(points, j, t);
            assert(false);
        }
    }
    if points[j][1] > max_y_smaller_encode(points, i, ej, n)
        && !(exists |t: int| 0 <= t < n && t != j && is_candidate(points, i, t)
            && encode(points[t][0], points[t][1]) == ej) {
        assert forall |t: int| 0 <= t < n && t != i && t != j && is_candidate(points, i, t)
            implies !(points[t][0] <= points[j][0] && points[j][1] <= points[t][1]) by {
            lemma_blocks_iff_encode(points, j, t);
            if points[t][0] <= points[j][0] && points[j][1] <= points[t][1] {
                if encode(points[t][0], points[t][1]) < ej {
                    assert(points[t][1] <= max_y_smaller_encode(points, i, ej, n));
                }
            }
        }
        assert(is_dominant(points, i, j));
    }
}

proof fn lemma_count_pred_push(s: Seq<int>, x: int, pred: spec_fn(int) -> bool)
    ensures count_pred(s.push(x), pred) == count_pred(s, pred) + (if pred(x) { 1int } else { 0int }),
{
    assert(s.push(x) =~= s + seq![x]);
    lemma_count_pred_split(s.push(x), s.len() as int, pred);
    assert(s.push(x).subrange(0, s.len() as int) =~= s);
    assert(s.push(x).subrange(s.len() as int, s.push(x).len() as int) =~= seq![x]);
    assert(seq![x].drop_first() =~= Seq::<int>::empty());
    assert(seq![x][0] == x);
    assert(count_pred(seq![x], pred) == (if pred(x) { 1int } else { 0int }) + count_pred(Seq::<int>::empty(), pred));
    assert(count_pred(Seq::<int>::empty(), pred) == 0);
    assert(count_pred(seq![x], pred) == (if pred(x) { 1int } else { 0int }));
    assert(count_pred(s.push(x), pred) == count_pred(s, pred) + (if pred(x) { 1int } else { 0int }));
}

pub open spec fn count_valid_candidates(points: Seq<Seq<int>>, i: int, n: int, s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if decode_y(s[0]) > max_y_smaller_encode(points, i, s[0], n)
            && count_candidates_with_val(points, i, n, s[0]) <= 1 { 1int } else { 0int })
            + count_valid_candidates(points, i, n, s.drop_first())
    }
}

proof fn lemma_count_valid_candidates_push(points: Seq<Seq<int>>, i: int, n: int, s: Seq<int>, x: int)
    ensures count_valid_candidates(points, i, n, s.push(x))
        == count_valid_candidates(points, i, n, s)
            + (if decode_y(x) > max_y_smaller_encode(points, i, x, n)
                && count_candidates_with_val(points, i, n, x) <= 1 { 1int } else { 0int }),
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(seq![x].drop_first() =~= Seq::<int>::empty());
        assert(seq![x][0] == x);
        assert(count_valid_candidates(points, i, n, s.push(x))
            == (if decode_y(x) > max_y_smaller_encode(points, i, x, n)
                && count_candidates_with_val(points, i, n, x) <= 1 { 1int } else { 0int })
                + count_valid_candidates(points, i, n, Seq::<int>::empty()));
    } else {
        lemma_count_valid_candidates_push(points, i, n, s.drop_first(), x);
        assert(s.push(x).drop_first() =~= s.drop_first().push(x));
        assert(s.push(x)[0] == s[0]);
        assert(count_valid_candidates(points, i, n, s.push(x))
            == (if decode_y(s[0]) > max_y_smaller_encode(points, i, s[0], n)
                && count_candidates_with_val(points, i, n, s[0]) <= 1 { 1int } else { 0int })
                + count_valid_candidates(points, i, n, s.push(x).drop_first()));
    }
    assert(count_valid_candidates(points, i, n, s.push(x))
        == count_valid_candidates(points, i, n, s)
            + (if decode_y(x) > max_y_smaller_encode(points, i, x, n)
                && count_candidates_with_val(points, i, n, x) <= 1 { 1int } else { 0int }));
}

proof fn lemma_count_valid_candidates_cons(points: Seq<Seq<int>>, i: int, n: int, x: int, rest: Seq<int>)
    ensures count_valid_candidates(points, i, n, seq![x] + rest)
        == (if decode_y(x) > max_y_smaller_encode(points, i, x, n)
            && count_candidates_with_val(points, i, n, x) <= 1 { 1int } else { 0int })
            + count_valid_candidates(points, i, n, rest),
{
    assert((seq![x] + rest).drop_first() =~= rest);
    assert((seq![x] + rest)[0] == x);
}

proof fn lemma_count_valid_candidates_split(points: Seq<Seq<int>>, i: int, n: int, s: Seq<int>, mid: int)
    requires 0 <= mid <= s.len(),
    ensures count_valid_candidates(points, i, n, s)
        == count_valid_candidates(points, i, n, s.subrange(0, mid))
            + count_valid_candidates(points, i, n, s.subrange(mid, s.len() as int)),
    decreases mid
{
    if mid == 0 {
        assert(s.subrange(0, 0) =~= Seq::<int>::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(s.len() > 0);
        lemma_count_valid_candidates_split(points, i, n, s.drop_first(), mid - 1);
        assert(s.drop_first().subrange(0, mid - 1) =~= s.subrange(1, mid));
        assert(s.drop_first().subrange(mid - 1, s.drop_first().len() as int) =~= s.subrange(mid, s.len() as int));
        assert(s.subrange(0, mid) =~= seq![s[0]] + s.subrange(1, mid));
        lemma_count_valid_candidates_cons(points, i, n, s[0], s.subrange(1, mid));
    }
}

proof fn lemma_merge_seq_count_valid_candidates(points: Seq<Seq<int>>, i: int, n: int, a: Seq<int>, b: Seq<int>)
    ensures count_valid_candidates(points, i, n, merge_seq(a, b))
        == count_valid_candidates(points, i, n, a) + count_valid_candidates(points, i, n, b),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_count_valid_candidates(points, i, n, a.drop_first(), b);
        lemma_count_valid_candidates_cons(points, i, n, a[0], merge_seq(a.drop_first(), b));
        lemma_count_valid_candidates_cons(points, i, n, a[0], a.drop_first());
    } else {
        lemma_merge_seq_count_valid_candidates(points, i, n, a, b.drop_first());
        lemma_count_valid_candidates_cons(points, i, n, b[0], merge_seq(a, b.drop_first()));
        lemma_count_valid_candidates_cons(points, i, n, b[0], b.drop_first());
    }
}

proof fn lemma_merge_sort_seq_count_valid_candidates(points: Seq<Seq<int>>, i: int, n: int, s: Seq<int>)
    ensures count_valid_candidates(points, i, n, merge_sort_seq(s)) == count_valid_candidates(points, i, n, s),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_count_valid_candidates(points, i, n, s.subrange(0, mid));
        lemma_merge_sort_seq_count_valid_candidates(points, i, n, s.subrange(mid, s.len() as int));
        lemma_merge_seq_count_valid_candidates(points, i, n, merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
        lemma_count_valid_candidates_split(points, i, n, s, mid);
    }
}

proof fn lemma_candidates_pred_eq_dominant(points: Seq<Seq<int>>, i: int, jend: int)
    requires 0 <= i < points.len(), 0 <= jend <= points.len(),
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
        forall |k: int| 0 <= k < points.len() ==> -1_000_000_000 <= #[trigger] points[k][0] <= 1_000_000_000
            && -1_000_000_000 <= points[k][1] <= 1_000_000_000,
    ensures count_valid_candidates(points, i, points.len() as int, candidates_upto(points, i, jend))
        == count_dominant_upto(points, i, jend),
    decreases jend
{
    let n = points.len() as int;
    if jend > 0 {
        lemma_candidates_pred_eq_dominant(points, i, jend - 1);
        if is_candidate(points, i, jend - 1) {
            let e = encode(points[jend - 1][0], points[jend - 1][1]);
            lemma_count_valid_candidates_push(points, i, n, candidates_upto(points, i, jend - 1), e);
            lemma_valid_enc_of_encode(points[jend - 1][0], points[jend - 1][1]);
            lemma_is_dominant_char(points, i, jend - 1);
            let j = jend - 1;
            lemma_encode_decode(points[j][0], points[j][1]);
            lemma_count_candidates_with_val_ge1(points, i, n, e, j);
            if count_candidates_with_val(points, i, n, e) <= 1 {
                if exists |t: int| 0 <= t < n && t != j && is_candidate(points, i, t)
                    && encode(points[t][0], points[t][1]) == e {
                    let t = choose |t: int| 0 <= t < n && t != j && is_candidate(points, i, t)
                        && encode(points[t][0], points[t][1]) == e;
                    lemma_count_candidates_with_val_two(points, i, n, e, j, t);
                    assert(false);
                }
            } else {
                lemma_count_candidates_with_val_split_excl(points, i, n, e, j);
                lemma_count_candidates_with_val_excl_zero_iff(points, i, n, e, j);
                lemma_count_candidates_with_val_excl_nonneg(points, i, n, e, j);
                if !(exists |t: int| 0 <= t < n && t != j && is_candidate(points, i, t)
                    && encode(points[t][0], points[t][1]) == e) {
                    assert(count_candidates_with_val_excl(points, i, n, e, j) == 0);
                    assert(false);
                }
            }
        } else {
            assert(candidates_upto(points, i, jend) =~= candidates_upto(points, i, jend - 1));
        }
    }
}

proof fn lemma_candidates_upto_contains(points: Seq<Seq<int>>, i: int, jend: int, v: int)
    requires 0 <= i < points.len(), 0 <= jend <= points.len(),
    ensures candidates_upto(points, i, jend).contains(v) <==> (
        exists |t: int| 0 <= t < jend && is_candidate(points, i, t)
            && encode(points[t][0], points[t][1]) == v
    ),
    decreases jend
{
    if jend > 0 {
        lemma_candidates_upto_contains(points, i, jend - 1, v);
        if is_candidate(points, i, jend - 1) {
            let e = encode(points[jend - 1][0], points[jend - 1][1]);
            assert(candidates_upto(points, i, jend) =~= candidates_upto(points, i, jend - 1) + seq![e]);
            assert(candidates_upto(points, i, jend).contains(v)
                <==> (candidates_upto(points, i, jend - 1).contains(v) || seq![e].contains(v))) by {
                lemma_seq_concat_contains_all_elements(candidates_upto(points, i, jend - 1), seq![e], v);
            }
            assert(seq![e][0] == e);
            if seq![e].contains(v) {
                let k = choose |k: int| 0 <= k < seq![e].len() && seq![e][k] == v;
                assert(k == 0);
            }
            assert(seq![e].contains(v) <==> v == e);
            assert(candidates_upto(points, i, jend).contains(v) <==> (
                exists |t: int| 0 <= t < jend && is_candidate(points, i, t)
                    && encode(points[t][0], points[t][1]) == v
            ));
        } else {
            assert(candidates_upto(points, i, jend) =~= candidates_upto(points, i, jend - 1));
            assert(candidates_upto(points, i, jend).contains(v) <==> (
                exists |t: int| 0 <= t < jend && is_candidate(points, i, t)
                    && encode(points[t][0], points[t][1]) == v
            ));
        }
    }
}

pub open spec fn count_eq_val(s: Seq<int>, v: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == v { 1int } else { 0int }) + count_eq_val(s.drop_first(), v)
    }
}

proof fn lemma_count_eq_val_eq_count_pred(s: Seq<int>, v: int)
    ensures count_eq_val(s, v) == count_pred(s, |x: int| x == v),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_eq_val_eq_count_pred(s.drop_first(), v);
    }
}

proof fn lemma_count_eq_val_push(s: Seq<int>, x: int, v: int)
    ensures count_eq_val(s.push(x), v) == count_eq_val(s, v) + (if x == v { 1int } else { 0int }),
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(seq![x].drop_first() =~= Seq::<int>::empty());
        assert(seq![x][0] == x);
        assert(count_eq_val(s.push(x), v) == (if x == v { 1int } else { 0int }) + count_eq_val(Seq::<int>::empty(), v));
    } else {
        lemma_count_eq_val_push(s.drop_first(), x, v);
        assert(s.push(x).drop_first() =~= s.drop_first().push(x));
        assert(s.push(x)[0] == s[0]);
        assert(count_eq_val(s.push(x), v)
            == (if s[0] == v { 1int } else { 0int }) + count_eq_val(s.push(x).drop_first(), v));
    }
    assert(count_eq_val(s.push(x), v) == count_eq_val(s, v) + (if x == v { 1int } else { 0int }));
}

proof fn lemma_count_eq_val_nonneg(s: Seq<int>, v: int)
    ensures count_eq_val(s, v) >= 0,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_eq_val_nonneg(s.drop_first(), v);
    }
}

proof fn lemma_count_eq_val_cons(x: int, rest: Seq<int>, v: int)
    ensures count_eq_val(seq![x] + rest, v) == (if x == v { 1int } else { 0int }) + count_eq_val(rest, v),
{
    assert((seq![x] + rest).drop_first() =~= rest);
    assert((seq![x] + rest)[0] == x);
}

proof fn lemma_merge_seq_count_eq_val(a: Seq<int>, b: Seq<int>, v: int)
    ensures count_eq_val(merge_seq(a, b), v) == count_eq_val(a, v) + count_eq_val(b, v),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_count_eq_val(a.drop_first(), b, v);
        lemma_count_eq_val_cons(a[0], merge_seq(a.drop_first(), b), v);
        lemma_count_eq_val_cons(a[0], a.drop_first(), v);
    } else {
        lemma_merge_seq_count_eq_val(a, b.drop_first(), v);
        lemma_count_eq_val_cons(b[0], merge_seq(a, b.drop_first()), v);
        lemma_count_eq_val_cons(b[0], b.drop_first(), v);
    }
}

proof fn lemma_count_eq_val_split(s: Seq<int>, mid: int, v: int)
    requires 0 <= mid <= s.len(),
    ensures count_eq_val(s, v) == count_eq_val(s.subrange(0, mid), v) + count_eq_val(s.subrange(mid, s.len() as int), v),
    decreases mid
{
    if mid == 0 {
        assert(s.subrange(0, 0) =~= Seq::<int>::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(s.len() > 0);
        lemma_count_eq_val_split(s.drop_first(), mid - 1, v);
        assert(s.drop_first().subrange(0, mid - 1) =~= s.subrange(1, mid));
        assert(s.drop_first().subrange(mid - 1, s.drop_first().len() as int) =~= s.subrange(mid, s.len() as int));
        assert(s.subrange(0, mid) =~= seq![s[0]] + s.subrange(1, mid));
        lemma_count_eq_val_cons(s[0], s.subrange(1, mid), v);
    }
}

proof fn lemma_merge_sort_seq_count_eq_val(s: Seq<int>, v: int)
    ensures count_eq_val(merge_sort_seq(s), v) == count_eq_val(s, v),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_count_eq_val(s.subrange(0, mid), v);
        lemma_merge_sort_seq_count_eq_val(s.subrange(mid, s.len() as int), v);
        lemma_merge_seq_count_eq_val(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), v);
        lemma_count_eq_val_split(s, mid, v);
    }
}

proof fn lemma_count_eq_val_zero_iff_not_contains(s: Seq<int>, v: int)
    ensures count_eq_val(s, v) == 0 <==> !s.contains(v),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_eq_val_zero_iff_not_contains(s.drop_first(), v);
        assert(s =~= seq![s[0]] + s.drop_first());
        assert(s.contains(v) <==> (seq![s[0]].contains(v) || s.drop_first().contains(v))) by {
            lemma_seq_concat_contains_all_elements(seq![s[0]], s.drop_first(), v);
        }
        assert(seq![s[0]][0] == s[0]);
        if seq![s[0]].contains(v) {
            let k = choose |k: int| 0 <= k < seq![s[0]].len() && seq![s[0]][k] == v;
            assert(k == 0);
        }
        assert(seq![s[0]].contains(v) <==> v == s[0]);
        lemma_count_eq_val_nonneg(s.drop_first(), v);
    }
}

proof fn lemma_count_eq_val_at_least_one(s: Seq<int>, idx: int, v: int)
    requires 0 <= idx < s.len(), s[idx] == v,
    ensures count_eq_val(s, v) >= 1,
    decreases s.len()
{
    if idx == 0 {
    } else {
        lemma_count_eq_val_at_least_one(s.drop_first(), idx - 1, v);
        assert(s.drop_first()[idx - 1] == s[idx]);
    }
    lemma_count_eq_val_nonneg(s.drop_first(), v);
}

proof fn lemma_count_eq_val_two_equal_indices(s: Seq<int>, a: int, b: int)
    requires 0 <= a < b < s.len(), s[a] == s[b],
    ensures count_eq_val(s, s[a]) >= 2,
    decreases s.len()
{
    let v = s[a];
    if a == 0 {
        assert(s.drop_first()[b - 1] == s[b]);
        assert(s.drop_first()[b - 1] == v);
        lemma_count_eq_val_at_least_one(s.drop_first(), b - 1, v);
    } else {
        lemma_count_eq_val_two_equal_indices(s.drop_first(), a - 1, b - 1);
        assert(s.drop_first()[a - 1] == v);
    }
}

proof fn lemma_sorted_perm_unique(s1: Seq<int>, s2: Seq<int>)
    requires
        sorted_asc(s1),
        sorted_asc(s2),
        s1.len() == s2.len(),
        forall |v: int| count_eq_val(s1, v) == count_eq_val(s2, v),
    ensures s1 =~= s2,
    decreases s1.len(),
{
    if s1.len() > 0 {
        lemma_count_eq_val_at_least_one(s1, 0, s1[0]);
        assert(count_eq_val(s1, s1[0]) >= 1);
        assert(count_eq_val(s2, s1[0]) >= 1);
        lemma_count_eq_val_zero_iff_not_contains(s2, s1[0]);
        assert(s2.contains(s1[0]));
        let idx1 = choose |idx: int| 0 <= idx < s2.len() && s2[idx] == s1[0];
        assert(s2[0] <= s2[idx1]);

        lemma_count_eq_val_at_least_one(s2, 0, s2[0]);
        assert(count_eq_val(s2, s2[0]) >= 1);
        assert(count_eq_val(s1, s2[0]) >= 1);
        lemma_count_eq_val_zero_iff_not_contains(s1, s2[0]);
        assert(s1.contains(s2[0]));
        let idx2 = choose |idx: int| 0 <= idx < s1.len() && s1[idx] == s2[0];
        assert(s1[0] <= s1[idx2]);

        assert(s2[0] <= s1[0]);
        assert(s1[0] <= s2[0]);
        assert(s1[0] == s2[0]);

        lemma_sorted_drop_first(s1);
        lemma_sorted_drop_first(s2);
        assert forall |v: int| count_eq_val(s1.drop_first(), v) == count_eq_val(s2.drop_first(), v) by {
            assert(count_eq_val(s1, v) == (if s1[0] == v { 1int } else { 0int }) + count_eq_val(s1.drop_first(), v));
            assert(count_eq_val(s2, v) == (if s2[0] == v { 1int } else { 0int }) + count_eq_val(s2.drop_first(), v));
        }
        lemma_sorted_perm_unique(s1.drop_first(), s2.drop_first());
        assert(s1 =~= seq![s1[0]] + s1.drop_first());
        assert(s2 =~= seq![s2[0]] + s2.drop_first());
    }
}

proof fn lemma_max_y_prefix_char(s: Seq<int>, idx: int)
    requires 0 <= idx <= s.len(),
    ensures
        max_y_prefix(s, idx) != -2_000_000_001 ==> (
            exists |a: int| 0 <= a < idx && decode_y(s[a]) == max_y_prefix(s, idx)
        ),
        forall |a: int| 0 <= a < idx ==> #[trigger] decode_y(s[a]) <= max_y_prefix(s, idx),
    decreases idx
{
    if idx > 0 {
        lemma_max_y_prefix_char(s, idx - 1);
    }
}

proof fn lemma_count_eq_val_unique(s: Seq<int>, idx: int, v: int)
    requires 0 <= idx < s.len(), s[idx] == v,
        forall |b: int| 0 <= b < s.len() && b != idx ==> s[b] != v,
    ensures count_eq_val(s, v) == 1,
    decreases s.len()
{
    if idx == 0 {
        assert forall |b: int| 0 <= b < s.drop_first().len() implies s.drop_first()[b] != v by {
            assert(s.drop_first()[b] == s[b + 1]);
        }
        lemma_count_eq_val_zero_iff_not_contains(s.drop_first(), v);
        if s.drop_first().contains(v) {
            let k = choose |k: int| 0 <= k < s.drop_first().len() && s.drop_first()[k] == v;
            assert(false);
        }
    } else {
        assert(s[0] != v);
        assert forall |b: int| 0 <= b < s.drop_first().len() && b != idx - 1 implies s.drop_first()[b] != v by {
            assert(s.drop_first()[b] == s[b + 1]);
        }
        assert(s.drop_first()[idx - 1] == s[idx]);
        lemma_count_eq_val_unique(s.drop_first(), idx - 1, v);
    }
}

proof fn lemma_valid_idx_char(points: Seq<Seq<int>>, i: int, n: int, idx: int)
    requires 0 <= i < points.len(), 0 <= n <= points.len(),
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
        forall |k: int| 0 <= k < points.len() ==> -1_000_000_000 <= #[trigger] points[k][0] <= 1_000_000_000
            && -1_000_000_000 <= points[k][1] <= 1_000_000_000,
        0 <= idx < merge_sort_seq(candidates_upto(points, i, n)).len(),
    ensures {
        let s = merge_sort_seq(candidates_upto(points, i, n));
        let v = s[idx];
        (decode_y(v) > max_y_prefix(s, idx) && (idx + 1 == s.len() || s[idx + 1] != v))
        <==> (decode_y(v) > max_y_smaller_encode(points, i, v, n)
            && count_candidates_with_val(points, i, n, v) <= 1)
    },
{
    let s = merge_sort_seq(candidates_upto(points, i, n));
    let v = s[idx];
    lemma_merge_sort_seq_sorted(candidates_upto(points, i, n));
    lemma_max_y_prefix_char(s, idx);
    lemma_max_y_smaller_encode_char(points, i, v, n);

    assert(s.contains(v));
    lemma_merge_sort_seq_contains(candidates_upto(points, i, n), v);
    lemma_candidates_upto_contains(points, i, n, v);
    let t0 = choose |t: int| 0 <= t < n && is_candidate(points, i, t)
        && encode(points[t][0], points[t][1]) == v;
    lemma_count_candidates_with_val_ge1(points, i, n, v, t0);

    if exists |a: int| 0 <= a < idx && s[a] == v {
        let a = choose |a: int| 0 <= a < idx && s[a] == v;
        assert(decode_y(s[a]) <= max_y_prefix(s, idx));
        assert(decode_y(v) <= max_y_prefix(s, idx));
        lemma_count_eq_val_two_equal_indices(s, a, idx);
        assert(count_eq_val(s, v) >= 2);
        lemma_merge_sort_seq_count_eq_val(candidates_upto(points, i, n), v);
        lemma_count_eq_val_candidates_upto(points, i, n, v);
        assert(count_candidates_with_val(points, i, n, v) >= 2);
    } else {
        assert forall |a: int| 0 <= a < idx implies s[a] < v by {
            assert(s[a] != v);
        }
        if max_y_prefix(s, idx) != -2_000_000_001 {
            let a = choose |a: int| 0 <= a < idx && decode_y(s[a]) == max_y_prefix(s, idx);
            assert(s.contains(s[a]));
            lemma_merge_sort_seq_contains(candidates_upto(points, i, n), s[a]);
            lemma_candidates_upto_contains(points, i, n, s[a]);
            let t = choose |t: int| 0 <= t < n && is_candidate(points, i, t)
                && encode(points[t][0], points[t][1]) == s[a];
            lemma_valid_enc_of_encode(points[t][0], points[t][1]);
            assert(points[t][1] == decode_y(s[a]));
            assert(s[a] < v);
            assert(points[t][1] <= max_y_smaller_encode(points, i, v, n));
            assert(max_y_prefix(s, idx) <= max_y_smaller_encode(points, i, v, n));
        }
        if idx > 0 {
            assert(s[0] < v);
            assert(s.contains(s[0]));
            lemma_merge_sort_seq_contains(candidates_upto(points, i, n), s[0]);
            lemma_candidates_upto_contains(points, i, n, s[0]);
            let t = choose |t: int| 0 <= t < n && is_candidate(points, i, t)
                && encode(points[t][0], points[t][1]) == s[0];
            assert(is_candidate(points, i, t) && encode(points[t][0], points[t][1]) < v);
        }
        assert(max_y_prefix(s, idx) <= max_y_smaller_encode(points, i, v, n));

        if max_y_smaller_encode(points, i, v, n) != -2_000_000_001 {
            let t = choose |t: int| 0 <= t < n && is_candidate(points, i, t)
                && encode(points[t][0], points[t][1]) < v
                && points[t][1] == max_y_smaller_encode(points, i, v, n);
            let e = encode(points[t][0], points[t][1]);
            lemma_valid_enc_of_encode(points[t][0], points[t][1]);
            lemma_candidates_upto_contains(points, i, n, e);
            lemma_merge_sort_seq_contains(candidates_upto(points, i, n), e);
            assert(s.contains(e));
            let a = choose |a: int| 0 <= a < s.len() && s[a] == e;
            assert(e < v);
            if a >= idx {
                assert(s[idx] <= s[a]);
                assert(false);
            }
            assert(a < idx);
            assert(decode_y(s[a]) == points[t][1]);
            assert(decode_y(s[a]) <= max_y_prefix(s, idx));
            assert(max_y_smaller_encode(points, i, v, n) <= max_y_prefix(s, idx));
        }
        assert(max_y_prefix(s, idx) == max_y_smaller_encode(points, i, v, n));

        if idx + 1 == s.len() || s[idx + 1] != v {
            assert forall |b: int| 0 <= b < s.len() && b != idx implies s[b] != v by {
                if b < idx {
                } else if b > idx {
                    if b == idx + 1 {
                    } else {
                        assert(s[idx + 1] <= s[b]);
                    }
                }
            }
            lemma_count_eq_val_unique(s, idx, v);
            assert(count_eq_val(s, v) == 1);
            lemma_merge_sort_seq_count_eq_val(candidates_upto(points, i, n), v);
            lemma_count_eq_val_candidates_upto(points, i, n, v);
            assert(count_candidates_with_val(points, i, n, v) == 1);
        } else {
            lemma_count_eq_val_two_equal_indices(s, idx, idx + 1);
            assert(count_eq_val(s, v) >= 2);
            lemma_merge_sort_seq_count_eq_val(candidates_upto(points, i, n), v);
            lemma_count_eq_val_candidates_upto(points, i, n, v);
            assert(count_candidates_with_val(points, i, n, v) >= 2);
        }
    }
}

proof fn lemma_sweep_count_eq_count_pred_upto(points: Seq<Seq<int>>, i: int, box_idx: int)
    requires 0 <= i < points.len(),
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
        forall |k: int| 0 <= k < points.len() ==> -1_000_000_000 <= #[trigger] points[k][0] <= 1_000_000_000
            && -1_000_000_000 <= points[k][1] <= 1_000_000_000,
        0 <= box_idx <= merge_sort_seq(candidates_upto(points, i, points.len() as int)).len(),
    ensures sweep_count(merge_sort_seq(candidates_upto(points, i, points.len() as int)), box_idx)
        == count_valid_candidates(points, i, points.len() as int,
            merge_sort_seq(candidates_upto(points, i, points.len() as int)).subrange(0, box_idx)),
    decreases box_idx
{
    let n = points.len() as int;
    let s = merge_sort_seq(candidates_upto(points, i, n));
    if box_idx > 0 {
        lemma_sweep_count_eq_count_pred_upto(points, i, box_idx - 1);
        lemma_valid_idx_char(points, i, n, box_idx - 1);
        assert(s.subrange(0, box_idx) =~= s.subrange(0, box_idx - 1) + seq![s[box_idx - 1]]);
        lemma_count_valid_candidates_split(points, i, n, s.subrange(0, box_idx), box_idx - 1);
        assert(s.subrange(0, box_idx).subrange(0, box_idx - 1) =~= s.subrange(0, box_idx - 1));
        assert(s.subrange(0, box_idx).subrange(box_idx - 1, box_idx) =~= seq![s[box_idx - 1]]);
        lemma_count_valid_candidates_cons(points, i, n, s[box_idx - 1], Seq::<int>::empty());
        assert(seq![s[box_idx - 1]] =~= seq![s[box_idx - 1]] + Seq::<int>::empty());
        assert(sweep_count(s, box_idx) == sweep_count(s, box_idx - 1)
            + if decode_y(s[box_idx - 1]) > max_y_prefix(s, box_idx - 1)
                && (box_idx == s.len() || s[box_idx] != s[box_idx - 1]) { 1int } else { 0int });
    }
}

proof fn lemma_number_of_pairs_algo(points: Seq<Seq<int>>, i: int)
    requires 0 <= i < points.len(),
        forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
        forall |k: int| 0 <= k < points.len() ==> -1_000_000_000 <= #[trigger] points[k][0] <= 1_000_000_000
            && -1_000_000_000 <= points[k][1] <= 1_000_000_000,
    ensures {
        let n = points.len() as int;
        let s = merge_sort_seq(candidates_upto(points, i, n));
        sweep_count(s, s.len() as int) == Solution::count_j(points, i, n)
    },
{
    let n = points.len() as int;
    let s = merge_sort_seq(candidates_upto(points, i, n));
    lemma_sweep_count_eq_count_pred_upto(points, i, s.len() as int);
    assert(s.subrange(0, s.len() as int) =~= s);
    lemma_candidates_pred_eq_dominant(points, i, n);
    lemma_merge_sort_seq_count_valid_candidates(points, i, n, candidates_upto(points, i, n));
    lemma_count_j_eq_count_dominant(points, i, n);
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

pub open spec fn imin_nat(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

proof fn lemma_sorted_full_from_blocks(s: Seq<int>, width: int, n: int)
    requires
        0 < width, s.len() == n, n >= 0,
        forall |lo: int| 0 <= lo < n && lo % width == 0 ==>
            sorted_asc(#[trigger] s.subrange(lo, imin_nat(lo + width, n))),
        width >= n,
    ensures sorted_asc(s),
{
    if n > 0 {
        assert(0int % width == 0) by (nonlinear_arith)
            requires width > 0;
        assert(imin_nat(0 + width, n) == n);
        assert(sorted_asc(s.subrange(0, n)));
    }
    assert(s.subrange(0, n) =~= s);
}

fn merge_sort_exec(v: &Vec<i64>) -> (result: Vec<i64>)
    requires v.len() <= 1_000,
    ensures to_int_seq64(result@) == merge_sort_seq(to_int_seq64(v@)),
{
    let n = v.len();
    let ghost vv = to_int_seq64(v@);
    let mut a: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant n == v.len(), n <= 1000, k <= n, a.len() == k as int,
            forall |t: int| 0 <= t < k ==> a@[t] == v@[t],
        decreases n - k,
    {
        a.push(v[k]);
        k += 1;
    }
    proof {
        assert(a@ =~= v@);
    }
    let mut b: Vec<i64> = Vec::new();
    k = 0;
    while k < n
        invariant n == v.len(), n <= 1000, k <= n, b.len() == k as int,
        decreases n - k,
    {
        b.push(0i64);
        k += 1;
    }

    let mut width: usize = 1;
    while width < n
        invariant
            n == v.len(),
            n <= 1000,
            a.len() == n,
            b.len() == n,
            0 < width,
            forall |lo: int| 0 <= lo < n as int && lo % (width as int) == 0 ==>
                sorted_asc(#[trigger] to_int_seq64(a@).subrange(lo, imin_nat(lo + width as int, n as int))),
            forall |val: int| count_eq_val(to_int_seq64(a@), val) == count_eq_val(vv, val),
        decreases if width < n { (n - width) as int } else { 0int },
    {
        let ghost av_full = to_int_seq64(a@);
        let mut lo: usize = 0;
        while lo < n
            invariant
                n == v.len(),
                n <= 1000,
                width < n,
                a.len() == n,
                b.len() == n,
                to_int_seq64(a@) == av_full,
                lo <= n,
                lo as int % (2 * width as int) == 0 || lo == n,
                0 < width,
                forall |bo: int| 0 <= bo < n as int && bo % (width as int) == 0 ==>
                    sorted_asc(#[trigger] av_full.subrange(bo, imin_nat(bo + width as int, n as int))),
                forall |val: int| count_eq_val(to_int_seq64(b@).subrange(0, lo as int), val)
                    == count_eq_val(av_full.subrange(0, lo as int), val),
                forall |bo: int| 0 <= bo < lo as int && bo % (2 * width as int) == 0 ==>
                    sorted_asc(#[trigger] to_int_seq64(b@).subrange(bo, imin_nat(bo + 2 * width as int, n as int))),
            decreases n - lo,
        {
            let mid: usize = if lo + width < n { lo + width } else { n };
            let hi: usize = if lo + 2 * width < n { lo + 2 * width } else { n };
            let ghost left_seq = av_full.subrange(lo as int, mid as int);
            let ghost right_seq = av_full.subrange(mid as int, hi as int);
            proof {
                assert(left_seq =~= av_full.subrange(lo as int, mid as int));
                assert(right_seq =~= av_full.subrange(mid as int, hi as int));
                assert(lo < n);
                assert(imin_nat(lo as int + width as int, n as int) == mid as int);
                assert(lo as int % (2 * width as int) == 0);
                lemma_fundamental_div_mod(lo as int, 2 * width as int);
                let q = (lo as int) / (2 * width as int);
                assert(lo as int == (2 * width as int) * q);
                assert(lo as int == (2 * q) * (width as int) + 0) by (nonlinear_arith)
                    requires lo as int == (2 * width as int) * q;
                lemma_fundamental_div_mod_converse(lo as int, width as int, 2 * q, 0);
                assert(lo as int % (width as int) == 0);
                assert(sorted_asc(av_full.subrange(lo as int, imin_nat(lo as int + width as int, n as int))));
                assert(sorted_asc(left_seq));
                if mid < n {
                    assert(mid as int % (width as int) == 0) by (nonlinear_arith)
                        requires lo as int % (width as int) == 0, mid as int == lo as int + width as int;
                    assert(imin_nat(mid as int + width as int, n as int) == hi as int);
                    assert(sorted_asc(av_full.subrange(mid as int, imin_nat(mid as int + width as int, n as int))));
                    assert(sorted_asc(right_seq));
                } else {
                    assert(mid as int == n as int);
                    assert(hi as int == n as int);
                    assert(right_seq =~= Seq::<int>::empty());
                    assert(sorted_asc(right_seq));
                }
            }
            let mut i: usize = lo;
            let mut j: usize = mid;
            let mut k2: usize = lo;
            proof {
                assert(left_seq.skip(0) =~= left_seq);
                assert(right_seq.skip(0) =~= right_seq);
                assert(to_int_seq64(b@).subrange(lo as int, lo as int) =~= Seq::<int>::empty());
            }
            while k2 < hi
                invariant
                    n <= 1000,
                    hi <= n,
                    mid <= hi,
                    lo <= mid,
                    lo <= i <= mid,
                    mid <= j <= hi,
                    lo <= k2,
                    k2 == i + j - mid,
                    0 < width,
                    lo as int % (2 * width as int) == 0,
                    a.len() == n, b.len() == n,
                    to_int_seq64(a@) == av_full,
                    left_seq == av_full.subrange(lo as int, mid as int),
                    right_seq == av_full.subrange(mid as int, hi as int),
                    forall |val: int| count_eq_val(to_int_seq64(b@).subrange(0, lo as int), val)
                        == count_eq_val(av_full.subrange(0, lo as int), val),
                    forall |bo: int| 0 <= bo < lo as int && bo % (2 * width as int) == 0 ==>
                        sorted_asc(#[trigger] to_int_seq64(b@).subrange(bo, imin_nat(bo + 2 * width as int, n as int))),
                    to_int_seq64(b@).subrange(lo as int, k2 as int)
                        + merge_seq(left_seq.skip((i - lo) as int), right_seq.skip((j - mid) as int))
                        == merge_seq(left_seq, right_seq),
                decreases hi - k2,
            {
                let ghost b_pre = to_int_seq64(b@);
                let ghost b_pre_i64 = b@;
                if j >= hi || (i < mid && a[i] <= a[j]) {
                    proof {
                        assert(i < mid);
                        vstd::seq::lemma_seq_subrange_index_alt(av_full, lo as int, mid as int, i as int);
                        assert(left_seq[(i - lo) as int] == av_full[i as int]);
                        if j < hi {
                            vstd::seq::lemma_seq_subrange_index_alt(av_full, mid as int, hi as int, j as int);
                            assert(right_seq[(j - mid) as int] == av_full[j as int]);
                            assert(av_full[i as int] == a@[i as int] as int);
                            assert(av_full[j as int] == a@[j as int] as int);
                            assert((a@[i as int] as int) <= (a@[j as int] as int));
                            assert(left_seq[(i - lo) as int] <= right_seq[(j - mid) as int]);
                        }
                        assert((j - mid) as int >= right_seq.len() || left_seq[(i - lo) as int] <= right_seq[(j - mid) as int]);
                        lemma_merge_seq_skip_step_a(left_seq, right_seq, (i - lo) as int, (j - mid) as int);
                        assert(to_int_seq64(b@).subrange(lo as int, k2 as int).push(a@[i as int] as int)
                            =~= to_int_seq64(b@).subrange(lo as int, k2 as int) + seq![a@[i as int] as int]);
                    }
                    b.set(k2, a[i]);
                    proof {
                        assert(to_int_seq64(b@).subrange(lo as int, (k2 + 1) as int)
                            =~= to_int_seq64(b@).subrange(lo as int, k2 as int).push(a@[i as int] as int));
                        assert(b@ == b_pre_i64.update(k2 as int, a@[i as int]));
                        assert forall |m: int| 0 <= m < lo as int implies b@[m] == b_pre_i64[m] by {
                            vstd::seq::lemma_seq_update_different_alt(b_pre_i64, m, k2 as int, a@[i as int]);
                        }
                        assert(to_int_seq64(b@).subrange(0, lo as int) =~= b_pre.subrange(0, lo as int));
                        assert forall |bo: int| 0 <= bo < lo as int && bo % (2 * width as int) == 0 implies
                            #[trigger] to_int_seq64(b@).subrange(bo, imin_nat(bo + 2 * width as int, n as int))
                                =~= b_pre.subrange(bo, imin_nat(bo + 2 * width as int, n as int)) by {
                            lemma_fundamental_div_mod(bo, 2 * width as int);
                            lemma_fundamental_div_mod(lo as int, 2 * width as int);
                            let qb2 = bo / (2 * width as int);
                            let ql2 = (lo as int) / (2 * width as int);
                            assert(bo == (2 * width as int) * qb2);
                            assert(lo as int == (2 * width as int) * ql2);
                            assert(qb2 < ql2) by (nonlinear_arith)
                                requires
                                    bo == (2 * width as int) * qb2,
                                    lo as int == (2 * width as int) * ql2,
                                    bo < lo as int,
                                    width as int > 0;
                            assert(bo + 2 * width as int <= lo as int) by (nonlinear_arith)
                                requires
                                    lo as int == (2 * width as int) * ql2,
                                    bo == (2 * width as int) * qb2,
                                    qb2 < ql2,
                                    width as int > 0;
                            assert(imin_nat(bo + 2 * width as int, n as int) <= lo as int);
                            assert forall |m: int| bo <= m < imin_nat(bo + 2 * width as int, n as int) implies
                                to_int_seq64(b@)[m] == b_pre[m] by {
                                vstd::seq::lemma_seq_update_different_alt(b_pre_i64, m, k2 as int, a@[i as int]);
                            }
                        }
                    }
                    i += 1;
                } else {
                    proof {
                        assert(j < hi);
                        vstd::seq::lemma_seq_subrange_index_alt(av_full, mid as int, hi as int, j as int);
                        assert(right_seq[(j - mid) as int] == av_full[j as int]);
                        if i < mid {
                            vstd::seq::lemma_seq_subrange_index_alt(av_full, lo as int, mid as int, i as int);
                            assert(left_seq[(i - lo) as int] == av_full[i as int]);
                            assert(av_full[i as int] == a@[i as int] as int);
                            assert(av_full[j as int] == a@[j as int] as int);
                            assert((a@[j as int] as int) < (a@[i as int] as int));
                            assert(right_seq[(j - mid) as int] < left_seq[(i - lo) as int]);
                        }
                        assert((i - lo) as int >= left_seq.len() || right_seq[(j - mid) as int] < left_seq[(i - lo) as int]);
                        lemma_merge_seq_skip_step_b(left_seq, right_seq, (i - lo) as int, (j - mid) as int);
                        assert(to_int_seq64(b@).subrange(lo as int, k2 as int).push(a@[j as int] as int)
                            =~= to_int_seq64(b@).subrange(lo as int, k2 as int) + seq![a@[j as int] as int]);
                    }
                    b.set(k2, a[j]);
                    proof {
                        assert(to_int_seq64(b@).subrange(lo as int, (k2 + 1) as int)
                            =~= to_int_seq64(b@).subrange(lo as int, k2 as int).push(a@[j as int] as int));
                        assert(b@ == b_pre_i64.update(k2 as int, a@[j as int]));
                        assert forall |m: int| 0 <= m < lo as int implies b@[m] == b_pre_i64[m] by {
                            vstd::seq::lemma_seq_update_different_alt(b_pre_i64, m, k2 as int, a@[j as int]);
                        }
                        assert(to_int_seq64(b@).subrange(0, lo as int) =~= b_pre.subrange(0, lo as int));
                        assert forall |bo: int| 0 <= bo < lo as int && bo % (2 * width as int) == 0 implies
                            #[trigger] to_int_seq64(b@).subrange(bo, imin_nat(bo + 2 * width as int, n as int))
                                =~= b_pre.subrange(bo, imin_nat(bo + 2 * width as int, n as int)) by {
                            lemma_fundamental_div_mod(bo, 2 * width as int);
                            lemma_fundamental_div_mod(lo as int, 2 * width as int);
                            let qb2 = bo / (2 * width as int);
                            let ql2 = (lo as int) / (2 * width as int);
                            assert(bo == (2 * width as int) * qb2);
                            assert(lo as int == (2 * width as int) * ql2);
                            assert(qb2 < ql2) by (nonlinear_arith)
                                requires
                                    bo == (2 * width as int) * qb2,
                                    lo as int == (2 * width as int) * ql2,
                                    bo < lo as int,
                                    width as int > 0;
                            assert(bo + 2 * width as int <= lo as int) by (nonlinear_arith)
                                requires
                                    lo as int == (2 * width as int) * ql2,
                                    bo == (2 * width as int) * qb2,
                                    qb2 < ql2,
                                    width as int > 0;
                            assert(imin_nat(bo + 2 * width as int, n as int) <= lo as int);
                            assert forall |m: int| bo <= m < imin_nat(bo + 2 * width as int, n as int) implies
                                to_int_seq64(b@)[m] == b_pre[m] by {
                                vstd::seq::lemma_seq_update_different_alt(b_pre_i64, m, k2 as int, a@[j as int]);
                            }
                        }
                    }
                    j += 1;
                }
                k2 += 1;
            }
            proof {
                assert(left_seq.skip((i - lo) as int).len() == 0);
                assert(right_seq.skip((j - mid) as int).len() == 0);
                assert(merge_seq(left_seq.skip((i - lo) as int), right_seq.skip((j - mid) as int)) =~= Seq::<int>::empty());
                assert(to_int_seq64(b@).subrange(lo as int, hi as int) == merge_seq(left_seq, right_seq));
                lemma_merge_seq_sorted(left_seq, right_seq);
                lemma_merge_seq_count_eq_val(left_seq, right_seq, 0);
                assert forall |val: int| count_eq_val(to_int_seq64(b@).subrange(lo as int, hi as int), val)
                    == count_eq_val(left_seq, val) + count_eq_val(right_seq, val) by {
                    lemma_merge_seq_count_eq_val(left_seq, right_seq, val);
                }
                assert forall |val: int| count_eq_val(av_full.subrange(lo as int, hi as int), val)
                    == count_eq_val(left_seq, val) + count_eq_val(right_seq, val) by {
                    assert(av_full.subrange(lo as int, hi as int) =~= left_seq + right_seq);
                    lemma_count_eq_val_split(av_full.subrange(lo as int, hi as int), (mid - lo) as int, val);
                    assert(av_full.subrange(lo as int, hi as int).subrange(0, (mid - lo) as int) =~= left_seq);
                    assert(av_full.subrange(lo as int, hi as int).subrange((mid - lo) as int, (hi - lo) as int) =~= right_seq);
                }
                assert forall |val: int| count_eq_val(to_int_seq64(b@).subrange(0, hi as int), val)
                    == count_eq_val(av_full.subrange(0, hi as int), val) by {
                    lemma_count_eq_val_split(to_int_seq64(b@).subrange(0, hi as int), lo as int, val);
                    lemma_count_eq_val_split(av_full.subrange(0, hi as int), lo as int, val);
                    assert(to_int_seq64(b@).subrange(0, hi as int).subrange(0, lo as int)
                        =~= to_int_seq64(b@).subrange(0, lo as int));
                    assert(to_int_seq64(b@).subrange(0, hi as int).subrange(lo as int, hi as int)
                        =~= to_int_seq64(b@).subrange(lo as int, hi as int));
                    assert(av_full.subrange(0, hi as int).subrange(0, lo as int) =~= av_full.subrange(0, lo as int));
                    assert(av_full.subrange(0, hi as int).subrange(lo as int, hi as int)
                        =~= av_full.subrange(lo as int, hi as int));
                    assert(count_eq_val(to_int_seq64(b@).subrange(0, lo as int), val)
                        == count_eq_val(av_full.subrange(0, lo as int), val));
                    assert(count_eq_val(to_int_seq64(b@).subrange(lo as int, hi as int), val)
                        == count_eq_val(av_full.subrange(lo as int, hi as int), val));
                }
                assert(imin_nat(lo as int + 2 * width as int, n as int) == hi as int);
                assert(sorted_asc(to_int_seq64(b@).subrange(lo as int, hi as int)));
                assert forall |bo: int| 0 <= bo < hi as int && bo % (2 * width as int) == 0 implies
                    sorted_asc(#[trigger] to_int_seq64(b@).subrange(bo, imin_nat(bo + 2 * width as int, n as int))) by {
                    if bo < lo {
                        assert(sorted_asc(to_int_seq64(b@).subrange(bo, imin_nat(bo + 2 * width as int, n as int))));
                    } else {
                        assert(lo as int <= bo < hi as int);
                        assert(hi as int <= lo as int + 2 * width as int);
                        lemma_fundamental_div_mod(bo, 2 * width as int);
                        lemma_fundamental_div_mod(lo as int, 2 * width as int);
                        let qb = bo / (2 * width as int);
                        let ql = (lo as int) / (2 * width as int);
                        assert(bo == (2 * width as int) * qb);
                        assert(lo as int == (2 * width as int) * ql);
                        assert(qb == ql) by (nonlinear_arith)
                            requires
                                bo == (2 * width as int) * qb,
                                lo as int == (2 * width as int) * ql,
                                lo as int <= bo < lo as int + 2 * width as int,
                                width as int > 0;
                        assert(bo == lo as int);
                    }
                }
            }
            proof {
                if hi < n {
                    assert(hi as int == lo as int + 2 * width as int);
                    assert(hi as int % (2 * width as int) == 0) by (nonlinear_arith)
                        requires
                            lo as int % (2 * width as int) == 0,
                            hi as int == lo as int + 2 * width as int;
                }
            }
            lo = hi;
        }
        proof {
            assert(lo == n);
            assert(to_int_seq64(b@).subrange(0, n as int) =~= to_int_seq64(b@));
            assert(av_full.subrange(0, n as int) =~= av_full);
            assert forall |val: int| count_eq_val(to_int_seq64(b@), val) == count_eq_val(av_full, val) by {}
            assert forall |val: int| count_eq_val(to_int_seq64(b@), val) == count_eq_val(vv, val) by {}
        }
        let ghost half_width = width as int;
        let ghost b_final = to_int_seq64(b@);
        proof {
            assert forall |bo: int| 0 <= bo < n as int && bo % (2 * half_width) == 0 implies
                sorted_asc(#[trigger] b_final.subrange(bo, imin_nat(bo + 2 * half_width, n as int))) by {}
        }
        let tmp = a;
        a = b;
        b = tmp;
        width = width * 2;
        proof {
            assert(to_int_seq64(a@) == b_final);
            assert(width as int == 2 * half_width);
            assert forall |lo2: int| 0 <= lo2 < n as int && lo2 % (width as int) == 0 implies
                sorted_asc(#[trigger] to_int_seq64(a@).subrange(lo2, imin_nat(lo2 + width as int, n as int))) by {
                assert(lo2 % (2 * half_width) == 0);
                assert(sorted_asc(b_final.subrange(lo2, imin_nat(lo2 + 2 * half_width, n as int))));
            }
        }
    }
    proof {
        lemma_sorted_full_from_blocks(to_int_seq64(a@), width as int, n as int);
        assert forall |val: int| count_eq_val(to_int_seq64(a@), val) == count_eq_val(vv, val) by {}
        lemma_merge_sort_seq_sorted(vv);
        lemma_merge_sort_seq_len(vv);
        assert(merge_sort_seq(vv).len() == vv.len());
        assert(to_int_seq64(a@).len() == n as int);
        assert(vv.len() == n as int);
        assert forall |val: int| count_eq_val(merge_sort_seq(vv), val) == count_eq_val(vv, val) by {
            lemma_merge_sort_seq_count_eq_val(vv, val);
        }
        assert forall |val: int| count_eq_val(to_int_seq64(a@), val) == count_eq_val(merge_sort_seq(vv), val) by {
            assert(count_eq_val(to_int_seq64(a@), val) == count_eq_val(vv, val));
            assert(count_eq_val(merge_sort_seq(vv), val) == count_eq_val(vv, val));
        }
        lemma_sorted_perm_unique(to_int_seq64(a@), merge_sort_seq(vv));
    }
    a
}

fn encode_exec(x: i32, y: i32) -> (result: i64)
    requires -1_000_000_000 <= x <= 1_000_000_000, -1_000_000_000 <= y <= 1_000_000_000,
    ensures result as int == encode(x as int, y as int),
{
    proof {
        assert(0 <= x as i64 + 1_000_000_000 <= 2_000_000_000);
        assert((x as i64 + 1_000_000_000) * 2_000_000_003 <= 2_000_000_000 * 2_000_000_003) by (nonlinear_arith)
            requires 0 <= x as i64 + 1_000_000_000 <= 2_000_000_000;
    }
    (x as i64 + 1_000_000_000) * 2_000_000_003 + (1_000_000_000 - y as i64)
}

fn decode_y_exec(e: i64) -> (result: i64)
    requires 0 <= e <= 5_000_000_000_000_000_000i64,
    ensures result as int == decode_y(e as int),
{
    1_000_000_000 - (e % 2_000_000_003)
}

impl Solution {
    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 1000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len()
                ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                    && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i < j < points.len() ==> #[trigger] points[i] != #[trigger] points[j],
        ensures
            result as int == Self::spec_number_of_pairs(points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int))),
    {
        let n = points.len();
        let ghost pi = points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int));
        proof {
            assert(pi.len() == points@.len() as int);
            assert forall |k: int| 0 <= k < pi.len() implies #[trigger] pi[k].len() == 2 by {
                assert(pi[k] == points@[k]@.map_values(|v: i32| v as int));
                assert(pi[k].len() == points@[k]@.len());
                assert(points@[k].len() == 2);
            }
            assert forall |k: int| 0 <= k < pi.len() implies
                -1_000_000_000 <= #[trigger] pi[k][0] <= 1_000_000_000
                    && -1_000_000_000 <= pi[k][1] <= 1_000_000_000 by {
                assert(pi[k] == points@[k]@.map_values(|v: i32| v as int));
                assert(pi[k][0] == points@[k][0] as int);
                assert(pi[k][1] == points@[k][1] as int);
            }
        }
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == points.len(),
                2 <= points.len() <= 1000,
                pi == points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int)),
                pi.len() == points.len() as int,
                forall |k: int| 0 <= k < points.len() ==> #[trigger] points@[k].len() == 2,
                forall |k: int| 0 <= k < points.len()
                    ==> -1_000_000_000 <= #[trigger] points@[k][0] <= 1_000_000_000
                        && -1_000_000_000 <= points@[k][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < pi.len() ==> #[trigger] pi[k].len() == 2,
                forall |k: int| 0 <= k < pi.len()
                    ==> -1_000_000_000 <= #[trigger] pi[k][0] <= 1_000_000_000
                        && -1_000_000_000 <= pi[k][1] <= 1_000_000_000,
                total as int == Solution::count_i(pi, i as int),
                0 <= total <= 1_000_000,
            decreases n - i,
        {
            proof {
                assert(points@[i as int].len() == 2);
                assert(pi[i as int].len() == 2);
            }
            let xi = points[i][0];
            let yi = points[i][1];
            let mut cand: Vec<i64> = Vec::new();
            let mut t: usize = 0;
            while t < n
                invariant
                    0 <= t <= n,
                    n == points.len(),
                    2 <= points.len() <= 1000,
                    pi == points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int)),
                    pi.len() == points.len() as int,
                    0 <= i < n,
                    xi == points@[i as int][0],
                    yi == points@[i as int][1],
                    forall |k: int| 0 <= k < points.len() ==> #[trigger] points@[k].len() == 2,
                    forall |k: int| 0 <= k < points.len()
                        ==> -1_000_000_000 <= #[trigger] points@[k][0] <= 1_000_000_000
                            && -1_000_000_000 <= points@[k][1] <= 1_000_000_000,
                    forall |k: int| 0 <= k < pi.len() ==> #[trigger] pi[k].len() == 2,
                    forall |k: int| 0 <= k < pi.len()
                        ==> -1_000_000_000 <= #[trigger] pi[k][0] <= 1_000_000_000
                            && -1_000_000_000 <= pi[k][1] <= 1_000_000_000,
                    cand@.len() <= t,
                    to_int_seq64(cand@) == candidates_upto(pi, i as int, t as int),
                    forall |k: int| 0 <= k < cand@.len() ==> 0 <= #[trigger] cand@[k] <= 5_000_000_000_000_000_000i64,
                decreases n - t,
            {
                proof {
                    assert(points@[t as int].len() == 2);
                    assert(pi[t as int].len() == 2);
                    assert(pi[i as int] == points@[i as int]@.map_values(|v: i32| v as int));
                    assert(pi[i as int][0] == points@[i as int][0] as int);
                    assert(pi[i as int][1] == points@[i as int][1] as int);
                    assert(pi[i as int][0] == xi as int);
                    assert(pi[i as int][1] == yi as int);
                    assert(pi[t as int] == points@[t as int]@.map_values(|v: i32| v as int));
                    assert(pi[t as int][0] == points@[t as int][0] as int);
                    assert(pi[t as int][1] == points@[t as int][1] as int);
                }
                if t != i && xi <= points[t][0] && points[t][1] <= yi {
                    proof {
                        assert(is_candidate(pi, i as int, t as int));
                    }
                    let e = encode_exec(points[t][0], points[t][1]);
                    proof {
                        assert(e as int == encode(pi[t as int][0], pi[t as int][1]));
                        assert(candidates_upto(pi, i as int, t as int + 1)
                            == candidates_upto(pi, i as int, t as int).push(e as int));
                        assert(to_int_seq64(cand@.push(e)) =~= to_int_seq64(cand@).push(e as int));
                        assert(0 <= e <= 5_000_000_000_000_000_000i64);
                        assert forall |k: int| 0 <= k < cand@.push(e).len() implies
                            0 <= #[trigger] cand@.push(e)[k] <= 5_000_000_000_000_000_000i64 by {
                            if k < cand@.len() {
                                assert(cand@.push(e)[k] == cand@[k]);
                            } else {
                                assert(cand@.push(e)[k] == e);
                            }
                        }
                    }
                    cand.push(e);
                } else {
                    proof {
                        assert(!is_candidate(pi, i as int, t as int));
                        assert(candidates_upto(pi, i as int, t as int + 1)
                            == candidates_upto(pi, i as int, t as int));
                    }
                }
                t += 1;
            }
            let sorted_cand = merge_sort_exec(&cand);
            proof {
                assert(to_int_seq64(sorted_cand@) == merge_sort_seq(candidates_upto(pi, i as int, n as int)));
                lemma_merge_sort_seq_len(to_int_seq64(cand@));
                assert(sorted_cand@.len() == cand@.len());
                assert forall |k: int| 0 <= k < sorted_cand@.len() implies
                    0 <= #[trigger] sorted_cand@[k] <= 5_000_000_000_000_000_000i64 by {
                    assert(to_int_seq64(sorted_cand@).len() == sorted_cand@.len());
                    assert(to_int_seq64(sorted_cand@)[k] == sorted_cand@[k] as int);
                    assert(to_int_seq64(sorted_cand@).contains(sorted_cand@[k] as int));
                    lemma_merge_sort_seq_contains(to_int_seq64(cand@), sorted_cand@[k] as int);
                    assert(to_int_seq64(cand@).contains(sorted_cand@[k] as int));
                    let j = choose |j: int| 0 <= j < cand@.len() && to_int_seq64(cand@)[j] == sorted_cand@[k] as int;
                    assert(cand@[j] as int == sorted_cand@[k] as int);
                    assert(cand@[j] == sorted_cand@[k]);
                }
            }
            let m = sorted_cand.len();
            let mut prev_y: i64 = -2_000_000_001;
            let mut cnt: i64 = 0;
            let mut idx: usize = 0;
            while idx < m
                invariant
                    0 <= idx <= m,
                    m == sorted_cand.len(),
                    m <= 1000,
                    to_int_seq64(sorted_cand@) == merge_sort_seq(candidates_upto(pi, i as int, n as int)),
                    prev_y as int == max_y_prefix(to_int_seq64(sorted_cand@), idx as int),
                    cnt as int == sweep_count(to_int_seq64(sorted_cand@), idx as int),
                    -2_000_000_001 <= prev_y <= 1_000_000_000,
                    0 <= cnt <= idx,
                    forall |k: int| 0 <= k < sorted_cand@.len() ==> 0 <= #[trigger] sorted_cand@[k] <= 5_000_000_000_000_000_000i64,
                decreases m - idx,
            {
                proof {
                    assert(to_int_seq64(sorted_cand@)[idx as int] == sorted_cand@[idx as int] as int);
                    assert(0 <= sorted_cand@[idx as int] <= 5_000_000_000_000_000_000i64);
                }
                let y = decode_y_exec(sorted_cand[idx]);
                proof {
                    assert(y as int == decode_y(to_int_seq64(sorted_cand@)[idx as int]));
                }
                let has_next_dup = idx + 1 < m && sorted_cand[idx + 1] == sorted_cand[idx];
                proof {
                    assert(has_next_dup == (idx as int + 1 < to_int_seq64(sorted_cand@).len()
                        && to_int_seq64(sorted_cand@)[idx as int + 1] == to_int_seq64(sorted_cand@)[idx as int]));
                }
                let counted = y > prev_y && !has_next_dup;
                if y > prev_y {
                    prev_y = y;
                }
                if counted {
                    assert(cnt < m as i64);
                    cnt += 1;
                }
                proof {
                    assert(sweep_count(to_int_seq64(sorted_cand@), idx as int + 1)
                        == sweep_count(to_int_seq64(sorted_cand@), idx as int)
                            + if decode_y(to_int_seq64(sorted_cand@)[idx as int])
                                > max_y_prefix(to_int_seq64(sorted_cand@), idx as int)
                                && (idx as int + 1 == to_int_seq64(sorted_cand@).len()
                                    || to_int_seq64(sorted_cand@)[idx as int + 1]
                                        != to_int_seq64(sorted_cand@)[idx as int])
                                { 1int } else { 0int });
                    assert(max_y_prefix(to_int_seq64(sorted_cand@), idx as int + 1)
                        == {
                            let prev = max_y_prefix(to_int_seq64(sorted_cand@), idx as int);
                            let yv = decode_y(to_int_seq64(sorted_cand@)[idx as int]);
                            if yv > prev { yv } else { prev }
                        });
                }
                idx += 1;
            }
            proof {
                assert(to_int_seq64(sorted_cand@).len() == sorted_cand@.len());
                assert(cnt <= m as i64);
                assert(m <= 1000);
                lemma_number_of_pairs_algo(pi, i as int);
                assert(cnt as int == Solution::count_j(pi, i as int, n as int));
                assert(total as int + cnt as int == Solution::count_i(pi, i as int + 1));
                lemma_count_i_bound(pi, i as int + 1);
                assert(total as int + cnt as int <= (i as int + 1) * pi.len());
                assert(i as int + 1 <= 1000);
                assert(pi.len() <= 1000);
                assert((i as int + 1) * pi.len() <= 1_000_000) by (nonlinear_arith)
                    requires i as int + 1 <= 1000, pi.len() <= 1000, i as int + 1 >= 0, pi.len() >= 0;
                assert(total + cnt <= 1_000_000);
            }
            total = total + cnt;
            i += 1;
        }
        total as i32
    }
}

}
