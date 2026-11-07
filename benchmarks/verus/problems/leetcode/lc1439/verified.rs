use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_sums(mat: Seq<Vec<i32>>, row: int, col: int, remaining: int) -> nat
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
        if remaining >= 0 { 1 } else { 0 }
    } else if row < 0 || col >= mat[row].len() as int {
        0
    } else {
        count_sums(mat, row + 1, 0, remaining - mat[row][col] as int) +
        count_sums(mat, row, col + 1, remaining)
    }
}

pub open spec fn total_combos(mat: Seq<Vec<i32>>, row: int) -> int
    decreases mat.len() - row
{
    if row >= mat.len() as int { 1 }
    else { mat[row].len() as int * total_combos(mat, row + 1) }
}

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

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

pub open spec fn all_between(s: Seq<int>, lo: int, hi: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> lo <= #[trigger] s[i] <= hi
}

pub open spec fn rows_bounded(mat: Seq<Vec<i32>>) -> bool {
    forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
        1 <= #[trigger] mat[i][j] <= 5000
}

proof fn lemma_count_le_cons(x: int, rest: Seq<int>, v: int)
    ensures count_le(seq![x] + rest, v) == (if x <= v { 1int } else { 0int }) + count_le(rest, v),
{
    assert((seq![x] + rest).drop_first() =~= rest);
    assert((seq![x] + rest)[0] == x);
}

proof fn lemma_count_le_nonneg(s: Seq<int>, v: int)
    ensures count_le(s, v) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_le_nonneg(s.drop_first(), v);
    }
}

proof fn lemma_count_le_bound(s: Seq<int>, v: int)
    ensures count_le(s, v) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_le_bound(s.drop_first(), v);
    }
}

proof fn lemma_count_le_zero_when_gt(s: Seq<int>, v: int)
    requires
        sorted_asc(s),
        s.len() > 0 ==> s[0] > v,
    ensures
        count_le(s, v) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        assert(s[0] > v);
        if s.len() > 1 {
            assert(s.drop_first()[0] == s[1]);
            assert(s[0] <= s[1]);
            assert(s[1] > v);
            lemma_sorted_drop_first(s);
            lemma_count_le_zero_when_gt(s.drop_first(), v);
        }
        assert(count_le(s, v) == count_le(s.drop_first(), v));
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

proof fn lemma_take_unfold(s: Seq<int>, cap: int)
    requires 0 < cap <= s.len(),
    ensures s.take(cap) =~= seq![s[0]] + s.drop_first().take(cap - 1),
{
}

proof fn lemma_min_arith(cap: int, x: int, y: int)
    requires cap >= 0, x >= 0, y >= 0,
    ensures min_spec(cap, min_spec(cap, x) + min_spec(cap, y)) == min_spec(cap, x + y),
{
    if x <= cap && y <= cap {
        assert(min_spec(cap, x) == x);
        assert(min_spec(cap, y) == y);
        if x + y <= cap {
            assert(min_spec(cap, x + y) == x + y);
            assert(min_spec(cap, x + y) == x + y);
        } else {
            assert(min_spec(cap, x + y) == cap);
        }
    } else if x > cap {
        assert(min_spec(cap, x) == cap);
        assert(min_spec(cap, x + y) == cap);
    } else {
        assert(min_spec(cap, y) == cap);
        assert(min_spec(cap, x + y) == cap);
    }
}

proof fn lemma_min_step(cap: int, d: int, r: int)
    requires cap >= 1, 0 <= d <= 1, r >= 0, d == 0 ==> r == 0,
    ensures d + min_spec(cap - 1, r) == min_spec(cap, d + r),
{
    if d == 1 {
        if r <= cap - 1 {
            assert(min_spec(cap - 1, r) == r);
            assert(min_spec(cap, d + r) == d + r);
        } else {
            assert(min_spec(cap - 1, r) == cap - 1);
            assert(min_spec(cap, d + r) == cap);
        }
    } else {
        assert(r == 0);
        assert(min_spec(cap - 1, r) == 0);
        assert(min_spec(cap, d + r) == 0);
    }
}

proof fn lemma_sorted_take_count_le(s: Seq<int>, cap: int, v: int)
    requires sorted_asc(s), 0 <= cap <= s.len(),
    ensures count_le(s.take(cap), v) == min_spec(cap, count_le(s, v)),
    decreases s.len(),
{
    if cap == 0 {
        assert(s.take(0) =~= Seq::<int>::empty());
        lemma_count_le_nonneg(s, v);
    } else {
        lemma_take_unfold(s, cap);
        lemma_count_le_cons(s[0], s.drop_first().take(cap - 1), v);
        lemma_sorted_drop_first(s);
        lemma_sorted_take_count_le(s.drop_first(), cap - 1, v);
        lemma_count_le_nonneg(s.drop_first(), v);
        lemma_count_le_cons(s[0], s.drop_first(), v);
        let d: int = if s[0] <= v { 1int } else { 0int };
        let r = count_le(s.drop_first(), v);
        assert(count_le(s.take(cap), v) == d + min_spec(cap - 1, r));
        assert(count_le(s, v) == d + r);
        if s[0] > v {
            lemma_count_le_zero_when_gt(s.drop_first(), v);
            assert(r == 0);
        }
        lemma_min_step(cap, d, r);
        assert(d + min_spec(cap - 1, r) == min_spec(cap, d + r));
        assert(count_le(s.take(cap), v) == min_spec(cap, count_le(s, v)));
    }
}

pub open spec fn merge_capped(a: Seq<int>, b: Seq<int>, cap: int) -> Seq<int> {
    merge_seq(a, b).take(min_spec(cap, merge_seq(a, b).len() as int))
}

proof fn lemma_merge_capped_count_le(a: Seq<int>, b: Seq<int>, cap: int, v: int)
    requires sorted_asc(a), sorted_asc(b), cap >= 0,
    ensures count_le(merge_capped(a, b, cap), v) == min_spec(cap, count_le(a, v) + count_le(b, v)),
{
    lemma_merge_seq_sorted(a, b);
    lemma_merge_seq_len(a, b);
    lemma_merge_seq_count_le(a, b, v);
    let cap_eff = min_spec(cap, merge_seq(a, b).len() as int);
    lemma_sorted_take_count_le(merge_seq(a, b), cap_eff, v);
    lemma_count_le_nonneg(a, v);
    lemma_count_le_nonneg(b, v);
    lemma_count_le_bound(a, v);
    lemma_count_le_bound(b, v);
    assert(count_le(a, v) + count_le(b, v) <= merge_seq(a, b).len());
}

proof fn lemma_merge_capped_sorted(a: Seq<int>, b: Seq<int>, cap: int)
    requires sorted_asc(a), sorted_asc(b), cap >= 0,
    ensures sorted_asc(merge_capped(a, b, cap)),
{
    lemma_merge_seq_sorted(a, b);
}

proof fn lemma_merge_capped_len(a: Seq<int>, b: Seq<int>, cap: int)
    requires cap >= 0,
    ensures merge_capped(a, b, cap).len() == min_spec(cap, a.len() as int + b.len() as int),
{
    lemma_merge_seq_len(a, b);
}

proof fn lemma_merge_seq_all_between(a: Seq<int>, b: Seq<int>, lo: int, hi: int)
    requires all_between(a, lo, hi), all_between(b, lo, hi),
    ensures all_between(merge_seq(a, b), lo, hi),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_all_between(a.drop_first(), b, lo, hi);
    } else {
        lemma_merge_seq_all_between(a, b.drop_first(), lo, hi);
    }
}

proof fn lemma_take_all_between(s: Seq<int>, cap: int, lo: int, hi: int)
    requires all_between(s, lo, hi), 0 <= cap <= s.len(),
    ensures all_between(s.take(cap), lo, hi),
{
    assert forall|i: int| 0 <= i < s.take(cap).len() implies lo <= #[trigger] s.take(cap)[i] <= hi by {
        assert(s.take(cap)[i] == s[i]);
    }
}

proof fn lemma_merge_capped_all_between(a: Seq<int>, b: Seq<int>, cap: int, lo: int, hi: int)
    requires all_between(a, lo, hi), all_between(b, lo, hi), cap >= 0,
    ensures all_between(merge_capped(a, b, cap), lo, hi),
{
    lemma_merge_seq_all_between(a, b, lo, hi);
    lemma_merge_seq_len(a, b);
    let cap_eff = min_spec(cap, merge_seq(a, b).len() as int);
    lemma_take_all_between(merge_seq(a, b), cap_eff, lo, hi);
}

proof fn lemma_shift_seq_all_between(s: Seq<int>, shift: int, lo: int, hi: int)
    requires all_between(s, lo, hi),
    ensures all_between(shift_seq(s, shift), lo + shift, hi + shift),
{
    assert forall|i: int| 0 <= i < shift_seq(s, shift).len() implies
        lo + shift <= #[trigger] shift_seq(s, shift)[i] <= hi + shift by {
        assert(shift_seq(s, shift)[i] == shift + s[i]);
    }
}

pub open spec fn shift_seq(s: Seq<int>, shift: int) -> Seq<int> {
    s.map_values(|e: int| shift + e)
}

proof fn lemma_shift_seq_len(s: Seq<int>, shift: int)
    ensures shift_seq(s, shift).len() == s.len(),
{
}

proof fn lemma_shift_seq_sorted(s: Seq<int>, shift: int)
    requires sorted_asc(s),
    ensures sorted_asc(shift_seq(s, shift)),
{
    assert forall|i: int, j: int| 0 <= i <= j < shift_seq(s, shift).len() implies
        shift_seq(s, shift)[i] <= shift_seq(s, shift)[j] by {
        assert(shift_seq(s, shift)[i] == shift + s[i]);
        assert(shift_seq(s, shift)[j] == shift + s[j]);
    }
}

proof fn lemma_count_le_shift(s: Seq<int>, shift: int, v: int)
    ensures count_le(shift_seq(s, shift), v) == count_le(s, v - shift),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        assert(shift_seq(s, shift).drop_first() =~= shift_seq(s.drop_first(), shift));
        assert(shift_seq(s, shift)[0] == shift + s[0]);
        assert(shift_seq(s, shift) =~= seq![shift + s[0]] + shift_seq(s.drop_first(), shift));
        lemma_count_le_shift(s.drop_first(), shift, v);
        lemma_count_le_cons(shift + s[0], shift_seq(s.drop_first(), shift), v);
        lemma_count_le_cons(s[0], s.drop_first(), v - shift);
    }
}

pub open spec fn fold_cols(mat: Seq<Vec<i32>>, row: int, col: int, tail: Seq<int>, cap: int) -> Seq<int>
    decreases (if 0 <= row < mat.len() && col <= mat[row].len() { mat[row].len() - col } else { 0 }),
{
    if !(0 <= row < mat.len()) || col >= mat[row].len() {
        Seq::<int>::empty()
    } else {
        merge_capped(shift_seq(tail, mat[row][col] as int), fold_cols(mat, row, col + 1, tail, cap), cap)
    }
}

pub open spec fn capped_sums(mat: Seq<Vec<i32>>, row: int, cap: int) -> Seq<int>
    decreases mat.len() - row,
{
    if row >= mat.len() {
        seq![0int].take(min_spec(cap, 1))
    } else {
        fold_cols(mat, row, 0, capped_sums(mat, row + 1, cap), cap)
    }
}

pub open spec fn rows_sorted(mat: Seq<Vec<i32>>) -> bool {
    forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
        #[trigger] mat[i][j] <= mat[i][j + 1]
}

pub open spec fn rows_nonempty(mat: Seq<Vec<i32>>) -> bool {
    forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1
}

proof fn lemma_fold_cols_correct(mat: Seq<Vec<i32>>, row: int, col: int, cap: int, v: int)
    requires
        0 <= row < mat.len(),
        0 <= col <= mat[row].len(),
        cap >= 0,
        rows_sorted(mat),
        rows_nonempty(mat),
        rows_bounded(mat),
    ensures
        count_le(fold_cols(mat, row, col, capped_sums(mat, row + 1, cap), cap), v) ==
            min_spec(cap, count_sums(mat, row, col, v) as int),
        sorted_asc(fold_cols(mat, row, col, capped_sums(mat, row + 1, cap), cap)),
        fold_cols(mat, row, col, capped_sums(mat, row + 1, cap), cap).len() ==
            min_spec(cap, (mat[row].len() as int - col) * capped_sums(mat, row + 1, cap).len() as int),
        all_between(fold_cols(mat, row, col, capped_sums(mat, row + 1, cap), cap), 0,
            (mat.len() as int - row) * 5000),
    decreases mat.len() - row, mat[row].len() - col,
{
    let tail = capped_sums(mat, row + 1, cap);
    lemma_capped_sums_sorted(mat, row + 1, cap);
    lemma_capped_sums_len(mat, row + 1, cap);
    lemma_capped_sums_bound(mat, row + 1, cap);
    if col >= mat[row].len() {
        assert(fold_cols(mat, row, col, tail, cap) =~= Seq::<int>::empty());
        assert(col == mat[row].len());
        assert((mat[row].len() as int - col) * tail.len() as int == 0);
    } else {
        lemma_fold_cols_correct(mat, row, col + 1, cap, v);
        let val = mat[row][col] as int;
        lemma_capped_sums_correct(mat, row + 1, cap, v - val);
        lemma_shift_seq_sorted(tail, val);
        lemma_shift_seq_len(tail, val);
        lemma_merge_capped_count_le(shift_seq(tail, val), fold_cols(mat, row, col + 1, tail, cap), cap, v);
        lemma_merge_capped_sorted(shift_seq(tail, val), fold_cols(mat, row, col + 1, tail, cap), cap);
        lemma_merge_capped_len(shift_seq(tail, val), fold_cols(mat, row, col + 1, tail, cap), cap);
        lemma_count_le_shift(tail, val, v);
        assert(count_le(shift_seq(tail, val), v) == min_spec(cap, count_sums(mat, row + 1, 0, v - val) as int));
        assert(count_le(fold_cols(mat, row, col + 1, tail, cap), v) ==
            min_spec(cap, count_sums(mat, row, col + 1, v) as int));
        let x = count_sums(mat, row + 1, 0, v - val) as int;
        let y = count_sums(mat, row, col + 1, v) as int;
        lemma_min_arith(cap, x, y);
        assert(count_le(fold_cols(mat, row, col, tail, cap), v) == min_spec(cap, x + y));
        assert(count_sums(mat, row, col, v) as int == x + y);

        assert(tail.len() <= cap);
        lemma_min_arith(cap, tail.len() as int, (mat[row].len() as int - col - 1) * tail.len() as int);
        assert(fold_cols(mat, row, col, tail, cap).len() ==
            min_spec(cap, tail.len() as int + min_spec(cap, (mat[row].len() as int - col - 1) * tail.len() as int)));
        assert(tail.len() as int + (mat[row].len() as int - col - 1) * tail.len() as int ==
            (mat[row].len() as int - col) * tail.len() as int) by (nonlinear_arith);

        assert(1 <= val <= 5000);
        assert(all_between(tail, 0, (mat.len() as int - row - 1) * 5000));
        lemma_shift_seq_all_between(tail, val, 0, (mat.len() as int - row - 1) * 5000);
        assert(val + (mat.len() as int - row - 1) * 5000 <= (mat.len() as int - row) * 5000) by (nonlinear_arith)
            requires 1 <= val <= 5000;
        assert(all_between(shift_seq(tail, val), 0, (mat.len() as int - row) * 5000)) by {
            assert forall|idx: int| 0 <= idx < shift_seq(tail, val).len() implies
                0 <= #[trigger] shift_seq(tail, val)[idx] <= (mat.len() as int - row) * 5000 by {
                assert(val <= shift_seq(tail, val)[idx] <= val + (mat.len() as int - row - 1) * 5000);
            }
        }
        lemma_merge_capped_all_between(shift_seq(tail, val), fold_cols(mat, row, col + 1, tail, cap), cap,
            0, (mat.len() as int - row) * 5000);
    }
}

proof fn lemma_capped_sums_correct(mat: Seq<Vec<i32>>, row: int, cap: int, v: int)
    requires
        0 <= row <= mat.len(),
        cap >= 0,
        rows_sorted(mat),
        rows_nonempty(mat),
        rows_bounded(mat),
    ensures
        count_le(capped_sums(mat, row, cap), v) == min_spec(cap, count_sums(mat, row, 0, v) as int),
    decreases mat.len() - row, (if row < mat.len() { mat[row].len() + 1 } else { 0int }) as int,
{
    if row >= mat.len() {
        if cap >= 1 {
            assert(seq![0int].take(min_spec(cap, 1)) =~= seq![0int]);
            assert(seq![0int] =~= seq![0int] + Seq::<int>::empty());
            lemma_count_le_cons(0int, Seq::<int>::empty(), v);
        } else {
            assert(seq![0int].take(min_spec(cap, 1)) =~= Seq::<int>::empty());
        }
    } else {
        lemma_fold_cols_correct(mat, row, 0, cap, v);
    }
}

proof fn lemma_capped_sums_sorted(mat: Seq<Vec<i32>>, row: int, cap: int)
    requires
        0 <= row <= mat.len(),
        cap >= 0,
        rows_sorted(mat),
        rows_nonempty(mat),
        rows_bounded(mat),
    ensures
        sorted_asc(capped_sums(mat, row, cap)),
    decreases mat.len() - row, (if row < mat.len() { mat[row].len() + 1 } else { 0int }) as int,
{
    if row >= mat.len() {
    } else {
        lemma_fold_cols_correct(mat, row, 0, cap, 0);
    }
}

proof fn lemma_capped_sums_bound(mat: Seq<Vec<i32>>, row: int, cap: int)
    requires
        0 <= row <= mat.len(),
        cap >= 0,
        rows_sorted(mat),
        rows_nonempty(mat),
        rows_bounded(mat),
    ensures
        all_between(capped_sums(mat, row, cap), 0, (mat.len() as int - row) * 5000),
    decreases mat.len() - row, (if row < mat.len() { mat[row].len() + 1 } else { 0int }) as int,
{
    if row >= mat.len() {
        if cap >= 1 {
            assert(seq![0int].take(min_spec(cap, 1)) =~= seq![0int]);
        } else {
            assert(seq![0int].take(min_spec(cap, 1)) =~= Seq::<int>::empty());
        }
    } else {
        lemma_fold_cols_correct(mat, row, 0, cap, 0);
    }
}

proof fn lemma_min_mult(cap: int, k: int, t: int)
    requires cap >= 0, k >= 1, t >= 0,
    ensures min_spec(cap, k * min_spec(cap, t)) == min_spec(cap, k * t),
{
    if t <= cap {
    } else {
        assert(min_spec(cap, t) == cap);
        assert(k * cap >= cap) by (nonlinear_arith)
            requires k >= 1, cap >= 0;
        assert(min_spec(cap, k * cap) == cap);
        assert(k * t >= t) by (nonlinear_arith)
            requires k >= 1, t >= 0;
        assert(k * t > cap);
        assert(min_spec(cap, k * t) == cap);
    }
}

proof fn lemma_capped_sums_len(mat: Seq<Vec<i32>>, row: int, cap: int)
    requires
        0 <= row <= mat.len(),
        cap >= 0,
        rows_sorted(mat),
        rows_nonempty(mat),
        rows_bounded(mat),
    ensures
        capped_sums(mat, row, cap).len() == min_spec(cap, total_combos(mat, row)),
    decreases mat.len() - row, (if row < mat.len() { mat[row].len() + 1 } else { 0int }) as int,
{
    if row >= mat.len() {
        if cap >= 1 {
            assert(seq![0int].take(min_spec(cap, 1)) =~= seq![0int]);
        } else {
            assert(seq![0int].take(min_spec(cap, 1)) =~= Seq::<int>::empty());
        }
    } else {
        lemma_fold_cols_correct(mat, row, 0, cap, 0);
        lemma_capped_sums_len(mat, row + 1, cap);
        assert(mat[row].len() as int * capped_sums(mat, row + 1, cap).len() as int ==
            mat[row].len() as int * min_spec(cap, total_combos(mat, row + 1)));
        lemma_min_mult(cap, mat[row].len() as int, total_combos(mat, row + 1));
        assert(total_combos(mat, row) == mat[row].len() as int * total_combos(mat, row + 1));
    }
}

proof fn lemma_count_le_full(s: Seq<int>, v: int)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] <= v,
    ensures count_le(s, v) == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_le_full(s.drop_first(), v);
    }
}

proof fn lemma_count_le_lt_len_when_last_gt(s: Seq<int>, v: int)
    requires sorted_asc(s), s.len() > 0, s[s.len() - 1] > v,
    ensures count_le(s, v) < s.len(),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s[0] == s[s.len() - 1]);
        assert(s.drop_first() =~= Seq::<int>::empty());
        assert(count_le(s, v) == count_le(s.drop_first(), v));
    } else {
        lemma_sorted_drop_first(s);
        assert(s.drop_first()[s.drop_first().len() - 1] == s[s.len() - 1]);
        lemma_count_le_lt_len_when_last_gt(s.drop_first(), v);
        lemma_count_le_cons(s[0], s.drop_first(), v);
    }
}

proof fn lemma_kth_smallest_correct(mat: Seq<Vec<i32>>, k: int)
    requires
        1 <= mat.len(),
        rows_sorted(mat),
        rows_nonempty(mat),
        rows_bounded(mat),
        1 <= k,
        k <= total_combos(mat, 0),
    ensures
        capped_sums(mat, 0, k).len() == k,
        count_sums(mat, 0, 0, capped_sums(mat, 0, k)[k - 1]) >= k,
        count_sums(mat, 0, 0, (capped_sums(mat, 0, k)[k - 1] - 1) as int) < k,
        all_between(capped_sums(mat, 0, k), 0, mat.len() as int * 5000),
{
    lemma_capped_sums_len(mat, 0, k);
    lemma_capped_sums_sorted(mat, 0, k);
    lemma_capped_sums_bound(mat, 0, k);
    let l = capped_sums(mat, 0, k);
    assert(l.len() == k);
    let last = l[k - 1];
    let below = last - 1;
    lemma_count_le_full(l, last);
    lemma_capped_sums_correct(mat, 0, k, last);
    assert(min_spec(k, count_sums(mat, 0, 0, last) as int) == k);
    assert(count_sums(mat, 0, 0, last) as int >= k);

    lemma_count_le_lt_len_when_last_gt(l, below);
    lemma_capped_sums_correct(mat, 0, k, below);
    assert(min_spec(k, count_sums(mat, 0, 0, below) as int) < k);
    assert((count_sums(mat, 0, 0, below) as int) < k);
}


pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map_values(|x: i32| x as int)
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

proof fn lemma_prefix_take(x: Seq<int>, y: Seq<int>)
    ensures (x + y).take(x.len() as int) =~= x,
{
}

fn merge_capped_exec(a: &Vec<i32>, b: &Vec<i32>, cap: usize) -> (result: Vec<i32>)
    requires
        sorted_asc(to_int_seq(a@)),
        sorted_asc(to_int_seq(b@)),
        a.len() <= 1000,
        b.len() <= 1000,
    ensures
        to_int_seq(result@) == merge_capped(to_int_seq(a@), to_int_seq(b@), cap as int),
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
    while result.len() < cap && (i < a.len() || j < b.len())
        invariant
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j,
            result.len() <= cap,
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
        if i >= a.len() && j >= b.len() {
            assert(av.skip(i as int).len() == 0);
            assert(bv.skip(j as int).len() == 0);
            assert(merge_seq(av.skip(i as int), bv.skip(j as int)) =~= Seq::<int>::empty());
            assert(to_int_seq(result@) == merge_seq(av, bv));
            lemma_merge_seq_len(av, bv);
            assert(merge_seq(av, bv).len() == result.len());
            assert(merge_seq(av, bv).len() as int <= cap as int);
            assert(merge_capped(av, bv, cap as int) == merge_seq(av, bv).take(min_spec(cap as int, merge_seq(av, bv).len() as int)));
            assert(min_spec(cap as int, merge_seq(av, bv).len() as int) == merge_seq(av, bv).len() as int);
            assert(merge_seq(av, bv).take(merge_seq(av, bv).len() as int) =~= merge_seq(av, bv));
        } else {
            assert(result.len() == cap);
            lemma_merge_seq_len(av, bv);
            lemma_prefix_take(to_int_seq(result@), merge_seq(av.skip(i as int), bv.skip(j as int)));
            assert(merge_capped(av, bv, cap as int) == merge_seq(av, bv).take(min_spec(cap as int, merge_seq(av, bv).len() as int)));
            assert(min_spec(cap as int, merge_seq(av, bv).len() as int) == cap as int);
        }
    }
    result
}

fn shift_exec(s: &Vec<i32>, shift: i32) -> (result: Vec<i32>)
    requires
        all_between(to_int_seq(s@), 0, 1_000_000),
        0 <= shift <= 5000,
    ensures
        to_int_seq(result@) == shift_seq(to_int_seq(s@), shift as int),
{
    let ghost sv = to_int_seq(s@);
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < s.len()
        invariant
            idx <= s.len(),
            result.len() == idx,
            to_int_seq(s@) == sv,
            all_between(sv, 0, 1_000_000),
            0 <= shift <= 5000,
            forall|k: int| 0 <= k < idx ==> #[trigger] result@[k] as int == shift as int + sv[k],
        decreases s.len() - idx,
    {
        assert(sv[idx as int] == s@[idx as int] as int);
        assert(0 <= sv[idx as int] <= 1_000_000);
        assert(0 <= s@[idx as int] as int <= 1_000_000);
        assert(0 <= shift as int <= 5000);
        assert(s@[idx as int] as int + shift as int <= 1_005_000);
        result.push(s[idx] + shift);
        idx += 1;
    }
    assert(to_int_seq(result@) =~= shift_seq(sv, shift as int)) by {
        assert forall|k: int| 0 <= k < result.len() as int implies
            #[trigger] to_int_seq(result@)[k] == shift_seq(sv, shift as int)[k] by {
            assert(to_int_seq(result@)[k] == result@[k] as int);
            assert(shift_seq(sv, shift as int)[k] == shift as int + sv[k]);
        }
    }
    result
}

fn fold_cols_exec(mat: &Vec<Vec<i32>>, row: usize, tail: &Vec<i32>, cap: usize) -> (result: Vec<i32>)
    requires
        row < mat.len(),
        mat.len() <= 40,
        cap <= 200,
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1 && mat[i].len() <= 40,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            1 <= #[trigger] mat[i][j] <= 5000,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
        to_int_seq(tail@) == capped_sums(mat@, row as int + 1, cap as int),
    ensures
        to_int_seq(result@) == fold_cols(mat@, row as int, 0, to_int_seq(tail@), cap as int),
{
    proof {
        lemma_capped_sums_sorted(mat@, row as int + 1, cap as int);
        lemma_capped_sums_len(mat@, row as int + 1, cap as int);
        lemma_capped_sums_bound(mat@, row as int + 1, cap as int);
        assert((mat.len() as int - (row as int + 1)) * 5000 <= 200000) by (nonlinear_arith)
            requires mat.len() as int <= 40, row as int >= 0;
    }
    let ghost tv = to_int_seq(tail@);
    let n = mat[row].len();
    let mut acc: Vec<i32> = Vec::new();
    let mut c: usize = n;
    while c > 0
        invariant
            c <= n,
            n == mat[row as int].len(),
            row < mat.len(),
            mat.len() <= 40,
            cap <= 200,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1 && mat[i].len() <= 40,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
            to_int_seq(tail@) == tv,
            tv == capped_sums(mat@, row as int + 1, cap as int),
            sorted_asc(tv),
            all_between(tv, 0, 200000),
            tv.len() <= cap,
            to_int_seq(acc@) == fold_cols(mat@, row as int, c as int, tv, cap as int),
            sorted_asc(to_int_seq(acc@)),
            acc.len() <= cap,
        decreases c,
    {
        c -= 1;
        proof {
            assert(1 <= mat@[row as int][c as int] <= 5000);
        }
        let shifted = shift_exec(tail, mat[row][c]);
        proof {
            lemma_shift_seq_sorted(tv, mat@[row as int][c as int] as int);
            lemma_shift_seq_len(tv, mat@[row as int][c as int] as int);
            assert(to_int_seq(shifted@).len() == shift_seq(tv, mat@[row as int][c as int] as int).len());
            assert(shifted.len() == shifted@.len());
            assert(to_int_seq(shifted@).len() == shifted@.len());
            assert(shifted.len() == tv.len());
        }
        acc = merge_capped_exec(&shifted, &acc, cap);
        proof {
            lemma_fold_cols_correct(mat@, row as int, c as int, cap as int, 0);
            assert(acc.len() as int <= cap as int);
        }
    }
    acc
}

fn capped_sums_exec(mat: &Vec<Vec<i32>>, cap: usize) -> (result: Vec<i32>)
    requires
        1 <= mat.len() <= 40,
        cap <= 200,
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1 && mat[i].len() <= 40,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            1 <= #[trigger] mat[i][j] <= 5000,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
    ensures
        to_int_seq(result@) == capped_sums(mat@, 0, cap as int),
{
    let mut tail: Vec<i32> = Vec::new();
    if cap >= 1 {
        tail.push(0);
    }
    proof {
        if cap >= 1 {
            assert(seq![0int].take(min_spec(cap as int, 1)) =~= seq![0int]);
        } else {
            assert(seq![0int].take(min_spec(cap as int, 1)) =~= Seq::<int>::empty());
        }
        assert(to_int_seq(tail@) =~= capped_sums(mat@, mat.len() as int, cap as int));
    }
    let m = mat.len();
    let mut row: usize = m;
    while row > 0
        invariant
            row <= m,
            m == mat.len(),
            1 <= m <= 40,
            cap <= 200,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1 && mat[i].len() <= 40,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
            sorted_asc(to_int_seq(tail@)),
            all_between(to_int_seq(tail@), 0, (mat.len() as int - row as int) * 5000),
            tail.len() <= cap,
            to_int_seq(tail@) == capped_sums(mat@, row as int, cap as int),
        decreases row,
    {
        proof {
            lemma_capped_sums_len(mat@, row as int, cap as int);
            lemma_capped_sums_bound(mat@, row as int, cap as int);
            assert((mat.len() as int - row as int) * 5000 <= 200000) by (nonlinear_arith)
                requires mat.len() as int <= 40, row as int >= 0;
            assert(all_between(to_int_seq(tail@), 0, 200000));
        }
        row -= 1;
        tail = fold_cols_exec(mat, row, &tail, cap);
        proof {
            lemma_capped_sums_bound(mat@, row as int, cap as int);
            lemma_capped_sums_sorted(mat@, row as int, cap as int);
            lemma_capped_sums_len(mat@, row as int, cap as int);
        }
    }
    tail
}

impl Solution {
    pub fn kth_smallest(mat: Vec<Vec<i32>>, k: i32) -> (result: i32)
        requires
            1 <= mat.len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
            1 <= k <= 200,
            k as int <= total_combos(mat@, 0),
        ensures
            count_sums(mat@, 0, 0, result as int) >= k as int,
            count_sums(mat@, 0, 0, result as int - 1) < k as int,
    {
        proof {
            lemma_kth_smallest_correct(mat@, k as int);
        }
        let l = capped_sums_exec(&mat, k as usize);
        let ans = l[(k - 1) as usize];
        proof {
            assert(ans as int == capped_sums(mat@, 0, k as int)[k as int - 1]);
        }
        ans
    }
}

}
