use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

pub open spec fn spec_min_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2min(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2min(spec_i2min(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2min(
            spec_i2min(s[0] as int, s[1] as int),
            spec_i2min(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_max_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2max(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2max(spec_i2max(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2max(
            spec_i2max(s[0] as int, s[1] as int),
            spec_i2max(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_axis_span(s: Seq<i64>) -> int
    recommends
        s.len() == 4,
{
    spec_max_first_i(s, 4) - spec_min_first_i(s, 4)
}

impl Solution {
    pub fn axis_aligned_square_area(xs: Vec<i64>, ys: Vec<i64>) -> (res: i64)
        requires
            xs.len() == 4,
            ys.len() == 4,
            forall|j: int|
                0 <= j < 4 ==> -1000 <= (#[trigger] xs[j] as int) && (xs[j] as int) <= 1000 && -1000 <= (ys[j] as int) && (ys[j] as int) <= 1000,
            spec_axis_span(xs@) == spec_axis_span(ys@),
            spec_axis_span(xs@) > 0,
        ensures
            res as int == spec_axis_span(xs@) * spec_axis_span(ys@),
    {
    }
}

}
