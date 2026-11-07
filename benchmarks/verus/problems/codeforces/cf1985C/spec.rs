use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum(a: Seq<u64>, end: int) -> int
    recommends
        0 <= end <= a.len(),
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        prefix_sum(a, end - 1) + a[end - 1] as int
    }
}

pub open spec fn prefix_max(a: Seq<u64>, end: int) -> int
    recommends
        1 <= end <= a.len(),
    decreases end,
{
    if end <= 1 {
        a[0] as int
    } else {
        let prev = prefix_max(a, end - 1);
        let v = a[end - 1] as int;
        if v > prev { v } else { prev }
    }
}

pub open spec fn count_good_prefixes(a: Seq<u64>, end: int) -> int
    recommends
        0 <= end <= a.len(),
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        let prev = count_good_prefixes(a, end - 1);
        let s = prefix_sum(a, end);
        let m = prefix_max(a, end);
        if 2 * m == s {
            prev + 1
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn count_good_prefixes_fn(a: Vec<u64>) -> (result: usize)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1_000_000_000u64,
        ensures
            result as int == count_good_prefixes(a@, a.len() as int),
    {
    }
}

}
