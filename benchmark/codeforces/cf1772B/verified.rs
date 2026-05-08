use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_beautiful(a: i32, b: i32, c: i32, d: i32) -> bool {
    a < b && c < d && a < c && b < d
}

pub open spec fn can_make_beautiful_spec(a: i32, b: i32, c: i32, d: i32) -> bool {
    is_beautiful(a, b, c, d)
        || is_beautiful(c, a, d, b)
        || is_beautiful(d, c, b, a)
        || is_beautiful(b, d, a, c)
}

pub struct Solution;

impl Solution {
    pub fn can_make_beautiful(a: i32, b: i32, c: i32, d: i32) -> (res: bool)
        requires
            1 <= a && a <= 100,
            1 <= b && b <= 100,
            1 <= c && c <= 100,
            1 <= d && d <= 100,
            a != b,
            a != c,
            a != d,
            b != c,
            b != d,
            c != d,
        ensures
            res == can_make_beautiful_spec(a, b, c, d)
    {
        let res = ({
            (a < b && c < d && a < c && b < d)
                || (c < a && d < b && c < d && a < b)
                || (d < c && b < a && d < b && c < a)
                || (b < d && a < c && b < a && d < c)
        });
        proof {
            assert(res == can_make_beautiful_spec(a, b, c, d));
        }
        res
    }
}

}
