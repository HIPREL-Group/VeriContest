use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_min_int(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_taxi_answer(c1: int, c2: int, c3: int, c4: int) -> int {
    let c1_after_c3 = c1 - spec_min_int(c1, c3);
    let c2_half = (c2 + 1) / 2;
    let c1_after_c2 = if (c2 % 2) == 1 {
        c1_after_c3 - spec_min_int(2, c1_after_c3)
    } else {
        c1_after_c3
    };
    c4 + c3 + c2_half + (c1_after_c2 + 3) / 4
}

impl Solution {
    pub fn min_taxis(c1: i32, c2: i32, c3: i32, c4: i32) -> (res: i32)
        requires
            c1 >= 0,
            c2 >= 0,
            c3 >= 0,
            c4 >= 0,
            (c1 + c2 + c3 + c4) <= 100_000,
        ensures
            (res as int) == spec_taxi_answer(c1 as int, c2 as int, c3 as int, c4 as int),
    {
    }
}

}
