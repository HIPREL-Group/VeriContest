use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_seq(seq: Seq<i32>, n: int) -> int
    recommends 1 <= n <= seq.len(),
    decreases n,
{
    if n <= 1 {
        seq[0] as int
    } else {
        let prev = min_seq(seq, n - 1);
        if (seq[n - 1] as int) < prev { seq[n - 1] as int } else { prev }
    }
}

pub open spec fn has_value_strictly_greater(seq: Seq<i32>, n: int, m: int) -> bool {
    exists|i: int| 0 <= i < n && (#[trigger] seq[i]) as int > m
}

pub open spec fn is_smallest_above(seq: Seq<i32>, n: int, m: int, v: int) -> bool {
    (exists|i: int| 0 <= i < n && (#[trigger] seq[i]) as int == v && v > m)
    && (forall|j: int| 0 <= j < n ==> (#[trigger] seq[j]) as int <= m || (seq[j]) as int >= v)
}

impl Solution {
    pub fn second_min(a: Vec<i32>, n: usize) -> (result: Option<i32>)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> -100 <= #[trigger] a[i] as int <= 100,
        ensures
            ({
                let m = min_seq(a@, n as int);
                result.is_some() <==> has_value_strictly_greater(a@, n as int, m)
            }),
            result.is_some() ==> is_smallest_above(a@, n as int, min_seq(a@, n as int), result.unwrap() as int),
    {
    }
}

}
