use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_fixed_upto(p: Seq<i32>, hi: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0
    } else {
        let idx = hi - 1;
        count_fixed_upto(p, hi - 1) + if (p[idx] as int) == idx + 1 {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn min_swaps_spec(p: Seq<i32>) -> int {
    (count_fixed_upto(p, p.len() as int) + 1) / 2
}

pub struct Solution;

impl Solution {
    pub fn min_swaps(p: Vec<i32>) -> (result: i32)
        requires
            2 <= p.len() <= 100_000,
            forall|j: int|
                0 <= j < p.len() ==> 1 <= #[trigger] p[j] <= p.len() as int,
        ensures
            result as int == min_swaps_spec(p@),
    {
    }
}

}
