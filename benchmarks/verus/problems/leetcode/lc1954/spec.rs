use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn apples(r: int) -> int {
    2 * r * (r + 1) * (2 * r + 1)
}

impl Solution {
    pub fn minimum_perimeter(needed_apples: i64) -> (result: i64)
        requires
            1 <= needed_apples <= 1_000_000_000_000_000i64,
        ensures
            result >= 8,
            result % 8 == 0,
            apples(result as int / 8) >= needed_apples as int,
            forall |r: int| 0 < r < result as int / 8 ==> apples(r) < needed_apples as int,
    {
    }
}

}
