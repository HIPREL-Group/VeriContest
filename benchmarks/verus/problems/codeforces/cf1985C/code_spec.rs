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
        let mut sum: u64 = 0;
        let mut max_val: u64 = 0;
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < a.len() {
            let ai = a[i];
            sum = sum + ai;
            if ai > max_val {
                max_val = ai;
            }
            if 2 * max_val == sum {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}

}
