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
    }
}

}