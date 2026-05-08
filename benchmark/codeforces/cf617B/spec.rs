use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_nuts_range(a: Seq<i32>, lo: int, hi: int) -> int
    recommends
        0 <= lo && lo <= hi && hi <= a.len(),
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        (if (a[lo] as int) == 1 { 1int } else { 0int }) + count_nuts_range(a, lo + 1, hi)
    }
}

pub open spec fn count_nuts(a: Seq<i32>) -> int {
    count_nuts_range(a, 0, a.len() as int)
}

pub open spec fn last_nut_strictly_before(a: Seq<i32>, i: int) -> int
    recommends
        0 <= i && i <= a.len(),
    decreases i,
{
    if i <= 0 {
        -1
    } else if (a[i - 1] as int) == 1 {
        i - 1
    } else {
        last_nut_strictly_before(a, i - 1)
    }
}

pub open spec fn gap_product_prefix(a: Seq<i32>, end: int) -> int
    recommends
        0 <= end && end <= a.len(),
    decreases end,
{
    if end <= 0 {
        1
    } else if (a[end - 1] as int) == 0 {
        gap_product_prefix(a, end - 1)
    } else {
        let c = count_nuts_range(a, 0, end - 1);
        if c == 0 {
            1
        } else {
            let lastb = last_nut_strictly_before(a, end - 1);
            gap_product_prefix(a, end - 1) * ((end - 1) - lastb)
        }
    }
}

pub open spec fn chocolate_ways_spec(a: Seq<i32>) -> int {
    let k = count_nuts(a);
    if k == 0 {
        0
    } else if k == 1 {
        1
    } else {
        gap_product_prefix(a, a.len() as int)
    }
}

impl Solution {
    pub fn chocolate_ways(n: usize, a: Vec<i32>) -> (result: i128)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i < n ==> (#[trigger] (a[i] as int) == 0 || (a[i] as int) == 1),
        ensures
            result as int == chocolate_ways_spec(a@),
    {
    }
}

}
