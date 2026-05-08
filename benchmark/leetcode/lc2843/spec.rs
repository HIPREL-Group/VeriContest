use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_symmetric_num(x: int) -> bool {
        if 10 <= x <= 99 {
            x / 10 == x % 10
        } else if 1000 <= x <= 9999 {
            x / 1000 + (x / 100) % 10 == (x / 10) % 10 + x % 10
        } else {
            false
        }
    }

    pub open spec fn contrib(x: int) -> int {
        if Self::is_symmetric_num(x) { 1 } else { 0 }
    }

    pub open spec fn count_symmetric_range(low: int, high: int) -> int
        decreases if high < low { 0int } else { high - low + 1 }
    {
        if high < low {
            0
        } else {
            Self::count_symmetric_range(low, high - 1) + Self::contrib(high)
        }
    }

    pub fn count_symmetric_integers(low: i32, high: i32) -> (result: i32)
        requires
            1 <= low <= high <= 10_000,
        ensures
            result as int == Self::count_symmetric_range(low as int, high as int),
    {
    }
}

}
