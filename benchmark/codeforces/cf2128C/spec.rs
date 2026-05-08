use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_min2(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

pub open spec fn spec_min_range(b: Seq<i64>, hi: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0
    } else if hi == 1 {
        b[0] as int
    } else {
        spec_min2(spec_min_range(b, hi - 1), b[hi - 1] as int)
    }
}

pub open spec fn spec_leftmost_ok(b: Seq<i64>, n: int) -> bool {
    forall|k: int|
        1 <= k < n ==> (#[trigger] b[k] as int - spec_min_range(b, k) < spec_min_range(b, k))
}

pub struct Solution;

impl Solution {
    pub fn leftmost_below(n: usize, b: Vec<i64>) -> (res: bool)
        requires
            2 <= n <= 200000,
            n == b.len(),
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] b[i] <= 1000000000,
        ensures
            res == spec_leftmost_ok(b@, n as int),
    {
    }
}

}
