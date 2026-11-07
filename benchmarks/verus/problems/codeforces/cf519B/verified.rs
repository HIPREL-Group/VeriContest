use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_errors_valid(s: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000
}

pub open spec fn count_value(s: Seq<i64>, value: i64) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == value { 1int } else { 0int }) + count_value(s.subrange(1, s.len() as int), value)
    }
}

pub open spec fn seq_sum(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] as int + seq_sum(s.subrange(1, s.len() as int))
    }
}

pub open spec fn single_deletion(from: Seq<i64>, to: Seq<i64>, deleted: i64) -> bool {
    from.len() == to.len() + 1
        && forall|v: i64| #[trigger] count_value(from, v) == count_value(to, v) + if v == deleted { 1int } else { 0int }
}

pub open spec fn same_counts(left: Seq<i64>, right: Seq<i64>) -> bool {
    left.len() == right.len()
        && forall|v: i64| #[trigger] count_value(left, v) == count_value(right, v)
}

pub open spec fn remove_at(s: Seq<i64>, idx: int) -> Seq<i64>
    recommends
        0 <= idx < s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::<i64>::empty()
    } else if idx <= 0 {
        s.subrange(1, s.len() as int)
    } else {
        seq![s[0]] + remove_at(s.subrange(1, s.len() as int), idx - 1)
    }
}

proof fn lemma_count_value_nonnegative(s: Seq<i64>, value: i64)
    ensures
        0 <= count_value(s, value),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_value_nonnegative(s.subrange(1, s.len() as int), value);
    }
}

proof fn lemma_seq_sum_concat(left: Seq<i64>, right: Seq<i64>)
    ensures
        seq_sum(left + right) == seq_sum(left) + seq_sum(right),
    decreases left.len(),
{
    if left.len() == 0 {
    } else {
        let tail = left.subrange(1, left.len() as int);
        lemma_seq_sum_concat(tail, right);
        assert((left + right)[0] == left[0]);
        assert((left + right).subrange(1, (left + right).len() as int) =~= tail + right);
        assert(seq_sum(left + right) == left[0] as int + seq_sum(tail + right));
        assert(seq_sum(left) == left[0] as int + seq_sum(tail));
        assert(seq_sum(tail + right) == seq_sum(tail) + seq_sum(right));
    }
}

proof fn lemma_seq_sum_push(s: Seq<i64>, x: i64)
    ensures
        seq_sum(s.push(x)) == seq_sum(s) + x as int,
{
    assert(s.push(x) =~= s + seq![x]);
    lemma_seq_sum_concat(s, seq![x]);
    reveal_with_fuel(seq_sum, 2);
    assert(seq![x][0] == x);
    assert(seq![x].subrange(1, seq![x].len() as int) =~= Seq::<i64>::empty());
    assert(seq_sum(seq![x]) == x as int);
}

proof fn lemma_remove_at_len(s: Seq<i64>, idx: int)
    requires
        0 <= idx < s.len(),
    ensures
        remove_at(s, idx).len() + 1 == s.len(),
    decreases s.len(),
{
    if idx > 0 {
        lemma_remove_at_len(s.subrange(1, s.len() as int), idx - 1);
    }
}

proof fn lemma_count_implies_index(s: Seq<i64>, value: i64)
    requires
        count_value(s, value) > 0,
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == value,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(false);
    } else if s[0] == value {
        assert(exists|i: int| 0 <= i < s.len() && s[i] == value);
    } else {
        assert(count_value(s, value) == count_value(s.subrange(1, s.len() as int), value));
        lemma_count_implies_index(s.subrange(1, s.len() as int), value);
        let i = choose|i: int| 0 <= i < s.subrange(1, s.len() as int).len() && s.subrange(1, s.len() as int)[i] == value;
        assert(0 <= i + 1 < s.len());
        assert(s[i + 1] == value);
    }
}

proof fn lemma_count_value_remove_at(s: Seq<i64>, idx: int, value: i64)
    requires
        0 <= idx < s.len(),
    ensures
        count_value(s, value)
            == count_value(remove_at(s, idx), value) + if s[idx] == value { 1int } else { 0int },
    decreases s.len(),
{
    if idx == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        lemma_count_value_remove_at(tail, idx - 1, value);
        assert(remove_at(s, idx).subrange(1, remove_at(s, idx).len() as int) =~= remove_at(tail, idx - 1));
        if s[0] == value {
            assert(count_value(s, value) == 1 + count_value(tail, value));
            assert(count_value(remove_at(s, idx), value) == 1 + count_value(remove_at(tail, idx - 1), value));
        } else {
            assert(count_value(s, value) == count_value(tail, value));
            assert(count_value(remove_at(s, idx), value) == count_value(remove_at(tail, idx - 1), value));
        }
    }
}

proof fn lemma_seq_sum_remove_at(s: Seq<i64>, idx: int)
    requires
        0 <= idx < s.len(),
    ensures
        seq_sum(s) == seq_sum(remove_at(s, idx)) + s[idx] as int,
    decreases s.len(),
{
    if idx == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        lemma_seq_sum_remove_at(tail, idx - 1);
        assert(remove_at(s, idx).subrange(1, remove_at(s, idx).len() as int) =~= remove_at(tail, idx - 1));
        assert(seq_sum(s) == s[0] as int + seq_sum(tail));
        assert(seq_sum(remove_at(s, idx)) == s[0] as int + seq_sum(remove_at(tail, idx - 1)));
    }
}

proof fn lemma_same_counts_implies_equal_sum(s: Seq<i64>, t: Seq<i64>)
    requires
        same_counts(s, t),
    ensures
        seq_sum(s) == seq_sum(t),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let v = s[0];
        let s_tail = s.subrange(1, s.len() as int);
        assert(count_value(s, v) == count_value(s_tail, v) + 1);
        lemma_count_value_nonnegative(s_tail, v);
        assert(count_value(s, v) > 0);
        assert(count_value(t, v) == count_value(s, v));
        assert(count_value(t, v) > 0);
        lemma_count_implies_index(t, v);
        let j = choose|j: int| 0 <= j < t.len() && t[j] == v;
        let t_removed = remove_at(t, j);
        lemma_remove_at_len(t, j);
        lemma_count_value_remove_at(t, j, v);
        assert(s_tail.len() == t_removed.len());
        assert forall|x: i64| #[trigger] count_value(s_tail, x) == count_value(t_removed, x) by {
            lemma_count_value_remove_at(t, j, x);
            if x == v {
                assert(count_value(s, x) == count_value(s_tail, x) + 1);
                assert(count_value(t, x) == count_value(t_removed, x) + 1);
            } else {
                assert(count_value(s, x) == count_value(s_tail, x));
                assert(count_value(t, x) == count_value(t_removed, x));
            }
        }
        assert(same_counts(s_tail, t_removed));
        lemma_same_counts_implies_equal_sum(s_tail, t_removed);
        lemma_seq_sum_remove_at(t, j);
        assert(seq_sum(s) == v as int + seq_sum(s_tail));
        assert(seq_sum(t) == seq_sum(t_removed) + t[j] as int);
        assert(t[j] == v);
    }
}

proof fn lemma_single_deletion_sum(from: Seq<i64>, to: Seq<i64>, deleted: i64)
    requires
        single_deletion(from, to, deleted),
    ensures
        seq_sum(from) == seq_sum(to) + deleted as int,
{
    assert(count_value(from, deleted) == count_value(to, deleted) + 1);
    lemma_count_value_nonnegative(to, deleted);
    assert(count_value(from, deleted) > 0);
    lemma_count_implies_index(from, deleted);
    let i = choose|i: int| 0 <= i < from.len() && from[i] == deleted;
    let reduced = remove_at(from, i);
    lemma_remove_at_len(from, i);
    assert(reduced.len() == to.len());
    assert forall|x: i64| #[trigger] count_value(reduced, x) == count_value(to, x) by {
        lemma_count_value_remove_at(from, i, x);
        if x == deleted {
            assert(count_value(from, x) == count_value(reduced, x) + 1);
        } else {
            assert(count_value(from, x) == count_value(reduced, x));
        }
    }
    assert(same_counts(reduced, to));
    lemma_same_counts_implies_equal_sum(reduced, to);
    lemma_seq_sum_remove_at(from, i);
    assert(seq_sum(from) == seq_sum(reduced) + from[i] as int);
    assert(from[i] == deleted);
}

impl Solution {
    pub fn find_compilation_errors(first: Vec<i64>, second: Vec<i64>, third: Vec<i64>) -> (result: (i64, i64))
        requires
            3 <= first.len() <= 100_000,
            all_errors_valid(first@),
            all_errors_valid(second@),
            all_errors_valid(third@),
            exists|x: i64| single_deletion(first@, second@, x),
            exists|y: i64| single_deletion(second@, third@, y),
        ensures
            single_deletion(first@, second@, result.0),
            single_deletion(second@, third@, result.1),
    {
        let ghost x0 = choose|x: i64| single_deletion(first@, second@, x);
        let ghost y0 = choose|y: i64| single_deletion(second@, third@, y);
        proof {
            assert(second.len() + 1 == first.len());
            assert(third.len() + 1 == second.len());
        }

        let mut sum_first: i64 = 0;
        let mut i: usize = 0;
        while i < first.len()
            invariant
                3 <= first.len() <= 100_000,
                all_errors_valid(first@),
                0 <= i <= first.len(),
                sum_first as int == seq_sum(first@.subrange(0, i as int)),
                0 <= sum_first as int <= i as int * 1_000_000_000,
            decreases first.len() - i,
        {
            proof {
                let prefix = first@.subrange(0, i as int);
                lemma_seq_sum_push(prefix, first[i as int]);
                assert(first@.subrange(0, i as int + 1) =~= prefix.push(first[i as int]));
                assert(1 <= first[i as int] <= 1_000_000_000);
                assert(0 <= sum_first as int + first[i as int] as int <= (i as int + 1) * 1_000_000_000);
            }
            sum_first = sum_first + first[i];
            i = i + 1;
        }

        let mut sum_second: i64 = 0;
        let mut j: usize = 0;
        while j < second.len()
            invariant
                second.len() + 1 == first.len(),
                first.len() <= 100_000,
                all_errors_valid(second@),
                0 <= j <= second.len(),
                sum_second as int == seq_sum(second@.subrange(0, j as int)),
                0 <= sum_second as int <= j as int * 1_000_000_000,
            decreases second.len() - j,
        {
            proof {
                let prefix = second@.subrange(0, j as int);
                lemma_seq_sum_push(prefix, second[j as int]);
                assert(second@.subrange(0, j as int + 1) =~= prefix.push(second[j as int]));
                assert(1 <= second[j as int] <= 1_000_000_000);
                assert(0 <= sum_second as int + second[j as int] as int <= (j as int + 1) * 1_000_000_000);
            }
            sum_second = sum_second + second[j];
            j = j + 1;
        }

        let mut sum_third: i64 = 0;
        let mut k: usize = 0;
        while k < third.len()
            invariant
                third.len() + 1 == second.len(),
                second.len() + 1 == first.len(),
                first.len() <= 100_000,
                all_errors_valid(third@),
                0 <= k <= third.len(),
                sum_third as int == seq_sum(third@.subrange(0, k as int)),
                0 <= sum_third as int <= k as int * 1_000_000_000,
            decreases third.len() - k,
        {
            proof {
                let prefix = third@.subrange(0, k as int);
                lemma_seq_sum_push(prefix, third[k as int]);
                assert(third@.subrange(0, k as int + 1) =~= prefix.push(third[k as int]));
                assert(1 <= third[k as int] <= 1_000_000_000);
                assert(0 <= sum_third as int + third[k as int] as int <= (k as int + 1) * 1_000_000_000);
            }
            sum_third = sum_third + third[k];
            k = k + 1;
        }

        proof {
            assert(first@.subrange(0, first.len() as int) =~= first@);
            assert(second@.subrange(0, second.len() as int) =~= second@);
            assert(third@.subrange(0, third.len() as int) =~= third@);
            lemma_single_deletion_sum(first@, second@, x0);
            lemma_single_deletion_sum(second@, third@, y0);
            assert(sum_first as int == seq_sum(first@));
            assert(sum_second as int == seq_sum(second@));
            assert(sum_third as int == seq_sum(third@));
            assert(count_value(first@, x0) == count_value(second@, x0) + 1);
            lemma_count_value_nonnegative(second@, x0);
            assert(count_value(first@, x0) > 0);
            lemma_count_implies_index(first@, x0);
            let ix = choose|ix: int| 0 <= ix < first.len() && first[ix] == x0;
            assert(1 <= x0 <= 1_000_000_000);
            assert(count_value(second@, y0) == count_value(third@, y0) + 1);
            lemma_count_value_nonnegative(third@, y0);
            assert(count_value(second@, y0) > 0);
            lemma_count_implies_index(second@, y0);
            let iy = choose|iy: int| 0 <= iy < second.len() && second[iy] == y0;
            assert(1 <= y0 <= 1_000_000_000);
        }

        let deleted_first = sum_first - sum_second;
        let deleted_second = sum_second - sum_third;

        proof {
            assert(sum_first as int == seq_sum(first@));
            assert(sum_second as int == seq_sum(second@));
            assert(sum_third as int == seq_sum(third@));
            assert(deleted_first as int == seq_sum(first@) - seq_sum(second@));
            assert(deleted_second as int == seq_sum(second@) - seq_sum(third@));
            assert(deleted_first as int == x0 as int);
            assert(deleted_second as int == y0 as int);
            assert(deleted_first == x0);
            assert(deleted_second == y0);
            assert(single_deletion(first@, second@, deleted_first));
            assert(single_deletion(second@, third@, deleted_second));
        }

        (deleted_first, deleted_second)
    }
}

}
