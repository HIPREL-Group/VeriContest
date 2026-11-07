use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_count(s: Seq<i32>, i: int, v: int) -> int
    decreases i,
{
    if i <= 0 {
        0int
    } else {
        spec_prefix_count(s, i - 1, v) + if s[i - 1] as int == v {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn spec_has_duplicate(s: Seq<i32>) -> bool {
    exists|vv: int|
        #![trigger spec_prefix_count(s, s.len() as int, vv)]
        0 <= vv && vv <= 100 && spec_prefix_count(s, s.len() as int, vv) >= 2
}

pub open spec fn spec_min_ops_answer(s: Seq<i32>) -> int {
    let n = s.len() as int;
    let z = spec_prefix_count(s, n, 0);
    if z > 0 {
        n - z
    } else if spec_has_duplicate(s) {
        n
    } else {
        n + 1
    }
}

impl Solution {
    pub fn min_ops_to_all_zero(a: Vec<i32>) -> (res: i32)
        requires
            2 <= a.len() <= 100,
            forall|t: int|
                #![trigger a[t]]
                0 <= t < a.len() ==> 0 <= (a[t] as int) <= 100,
        ensures
            (res as int) == spec_min_ops_answer(a@),
    {
    }
}

}
