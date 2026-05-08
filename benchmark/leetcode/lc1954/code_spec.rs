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
        let mut lo: i64 = 1;
        let mut hi: i64 = 100_000;
        while lo < hi
        {
            let mid = lo + (hi - lo) / 2;
            let apples_mid = 2 * mid * (mid + 1) * (2 * mid + 1);
            if apples_mid >= needed_apples {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo * 8
    }
}

}
