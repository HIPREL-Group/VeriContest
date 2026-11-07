use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_strict_max_prefix(seq: Seq<i32>, i: int) -> bool
    recommends 0 <= i < seq.len(),
{
    forall|j: int| 0 <= j < i ==> seq[j] < seq[i]
}

pub open spec fn is_strict_min_prefix(seq: Seq<i32>, i: int) -> bool
    recommends 0 <= i < seq.len(),
{
    forall|j: int| 0 <= j < i ==> seq[j] > seq[i]
}

pub open spec fn is_amazing(seq: Seq<i32>, i: int) -> bool
    recommends 0 <= i < seq.len(),
{
    i > 0 && (is_strict_max_prefix(seq, i) || is_strict_min_prefix(seq, i))
}

pub open spec fn count_amazing_to(seq: Seq<i32>, end: int) -> nat
    recommends 0 <= end <= seq.len(),
    decreases end,
{
    if end <= 1 {
        0nat
    } else {
        let i = end - 1;
        let inc = if is_amazing(seq, i) { 1nat } else { 0nat };
        count_amazing_to(seq, end - 1) + inc
    }
}

pub open spec fn count_amazing(seq: Seq<i32>, n: int) -> nat
    recommends 0 <= n <= seq.len(),
{
    count_amazing_to(seq, n)
}

pub open spec fn seq_min(seq: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        if end <= 0 {
            0
        } else {
            seq[0] as int
        }
    } else {
        let prev = seq_min(seq, end - 1);
        let cur = seq[end - 1] as int;
        if prev <= cur {
            prev
        } else {
            cur
        }
    }
}

pub open spec fn seq_max(seq: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        if end <= 0 {
            0
        } else {
            seq[0] as int
        }
    } else {
        let prev = seq_max(seq, end - 1);
        let cur = seq[end - 1] as int;
        if prev >= cur {
            prev
        } else {
            cur
        }
    }
}

proof fn lemma_seq_max_ge(seq: Seq<i32>, end: int, j: int)
    requires
        end >= 1,
        end <= seq.len(),
        0 <= j < end,
    ensures
        seq[j] as int <= seq_max(seq, end),
    decreases end,
{
    reveal_with_fuel(seq_max, 2);
    if end > 1 && j < end - 1 {
        lemma_seq_max_ge(seq, end - 1, j);
    }
}

proof fn lemma_seq_min_le(seq: Seq<i32>, end: int, j: int)
    requires
        end >= 1,
        end <= seq.len(),
        0 <= j < end,
    ensures
        seq[j] as int >= seq_min(seq, end),
    decreases end,
{
    reveal_with_fuel(seq_min, 2);
    if end > 1 && j < end - 1 {
        lemma_seq_min_le(seq, end - 1, j);
    }
}

proof fn lemma_seq_max_in_prefix(seq: Seq<i32>, end: int)
    requires
        end >= 1,
        end <= seq.len(),
    ensures
        exists|j: int| 0 <= j < end && seq[j] as int == seq_max(seq, end),
    decreases end,
{
    reveal_with_fuel(seq_max, 2);
    if end == 1 {
        assert(seq[0] as int == seq_max(seq, 1));
    } else {
        lemma_seq_max_in_prefix(seq, end - 1);
        if seq_max(seq, end - 1) >= seq[end - 1] as int {
            assert(seq_max(seq, end) == seq_max(seq, end - 1));
        } else {
            assert(seq_max(seq, end) == seq[end - 1] as int);
        }
    }
}

proof fn lemma_seq_min_in_prefix(seq: Seq<i32>, end: int)
    requires
        end >= 1,
        end <= seq.len(),
    ensures
        exists|j: int| 0 <= j < end && seq[j] as int == seq_min(seq, end),
    decreases end,
{
    reveal_with_fuel(seq_min, 2);
    if end == 1 {
        assert(seq[0] as int == seq_min(seq, 1));
    } else {
        lemma_seq_min_in_prefix(seq, end - 1);
        if seq_min(seq, end - 1) <= seq[end - 1] as int {
            assert(seq_min(seq, end) == seq_min(seq, end - 1));
        } else {
            assert(seq_min(seq, end) == seq[end - 1] as int);
        }
    }
}

proof fn lemma_amazing_iff_max_or_min(seq: Seq<i32>, i: int)
    requires
        0 <= i < seq.len(),
        i > 0,
    ensures
        is_amazing(seq, i) <==> ((seq[i] as int) > seq_max(seq, i) || (seq[i] as int) < seq_min(seq, i)),
{
    reveal_with_fuel(is_amazing, 1);
    reveal_with_fuel(is_strict_max_prefix, 1);
    reveal_with_fuel(is_strict_min_prefix, 1);
    reveal_with_fuel(seq_max, 2);
    reveal_with_fuel(seq_min, 2);
    if (seq[i] as int) > seq_max(seq, i) {
        assert forall|j: int| 0 <= j < i implies seq[j] as int <= seq_max(seq, i) by {
            lemma_seq_max_ge(seq, i, j);
        };
        assert(forall|j: int| 0 <= j < i ==> seq[j] < seq[i]);
        assert(is_strict_max_prefix(seq, i));
        assert(is_amazing(seq, i));
    }
    if (seq[i] as int) < seq_min(seq, i) {
        assert forall|j: int| 0 <= j < i implies seq[j] as int >= seq_min(seq, i) by {
            lemma_seq_min_le(seq, i, j);
        };
        assert(forall|j: int| 0 <= j < i ==> seq[j] > seq[i]);
        assert(is_strict_min_prefix(seq, i));
        assert(is_amazing(seq, i));
    }
    if is_amazing(seq, i) {
        assert(is_strict_max_prefix(seq, i) || is_strict_min_prefix(seq, i));
        if is_strict_max_prefix(seq, i) {
            assert(forall|j: int| 0 <= j < i ==> seq[j] < seq[i]);
            lemma_seq_max_in_prefix(seq, i);
            let k = choose|j: int| 0 <= j < i && seq[j] as int == seq_max(seq, i);
            assert(seq[k] < seq[i]);
            assert((seq[i] as int) > seq_max(seq, i));
        }
        if is_strict_min_prefix(seq, i) {
            assert(forall|j: int| 0 <= j < i ==> seq[j] > seq[i]);
            lemma_seq_min_in_prefix(seq, i);
            let k = choose|j: int| 0 <= j < i && seq[j] as int == seq_min(seq, i);
            assert(seq[k] > seq[i]);
            assert((seq[i] as int) < (seq_min(seq, i)));
        }
    }
}

proof fn lemma_count_amazing_step(seq: Seq<i32>, end: int)
    requires
        1 <= end <= seq.len(),
    ensures
        count_amazing_to(seq, end)
            == count_amazing_to(seq, end - 1)
            + (if is_amazing(seq, end - 1) { 1nat } else { 0nat }),
    decreases end,
{
    reveal_with_fuel(count_amazing_to, 2);
}

impl Solution {
    pub fn count_amazing_performances(points: Vec<i32>, n: usize) -> (result: usize)
        requires
            1 <= n <= 1000,
            points.len() == n,
            forall|i: int| 0 <= i < points.len() as int ==> 0 <= #[trigger] points[i] as int <= 10000,
        ensures
            result as nat == count_amazing(points@, n as int),
            forall|i: int|
                1 <= i < n as int ==>
                (is_amazing(points@, i) <==> (is_strict_max_prefix(points@, i) || is_strict_min_prefix(points@, i))),
    {
        if n <= 1 {
            return 0;
        }
        let mut count = 0usize;
        let mut min_so_far = points[0];
        let mut max_so_far = points[0];
        let mut i = 1usize;
        while i < n
            invariant
                1 <= n <= 1000,
                1 <= i <= n,
                points.len() == n,
                points@.len() == n as int,
                count <= i,
                count as nat == count_amazing_to(points@, i as int),
                min_so_far as int == seq_min(points@, i as int),
                max_so_far as int == seq_max(points@, i as int),
            decreases
                n - i,
        {
            proof {
                lemma_amazing_iff_max_or_min(points@, i as int);
                lemma_count_amazing_step(points@, (i as int) + 1);
                assert(count <= i);
                assert(i <= n);
                assert(n <= 1000);
                assert((count as int) + 1 <= 1000);
                assert(1000 < 4294967296) by (nonlinear_arith);
                assert(1000 < 18446744073709551616 as int) by (nonlinear_arith);
            }
            if points[i] > max_so_far || points[i] < min_so_far {
                count += 1;
            }
            if points[i] > max_so_far {
                max_so_far = points[i];
            }
            if points[i] < min_so_far {
                min_so_far = points[i];
            }
            i += 1;
        }
        count
    }
}

}