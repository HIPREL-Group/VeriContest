use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn int_le(x: int, y: int) -> bool {
    x <= y
}

pub open spec fn spec_fashion_days(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_same_sock_days(a: int, b: int) -> int {
    if a >= b {
        (a - b) / 2
    } else {
        (b - a) / 2
    }
}

impl Solution {
    pub fn hipster_sock_days(a: i64, b: i64) -> (res: (i64, i64))
        requires
            1 <= a <= 100,
            1 <= b <= 100,
        ensures
            (res.0 as int) <= a as int && (res.0 as int) <= b as int,
            forall|t: int|
                #[trigger] int_le(t, a as int) && int_le(t, b as int) ==> int_le(t, (res.0 as int)),
            (res.0 as int) == spec_fashion_days(a as int, b as int),
            (res.1 as int) == spec_same_sock_days(a as int, b as int),
    {
    }
}

}
