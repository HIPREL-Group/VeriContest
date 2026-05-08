use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn repunit(n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else { repunit(n - 1) * 10 + 1 }
}

impl Solution {
    pub fn smallest_repunit_div_by_k(k: i32) -> (result: i32)
        requires
            1 <= k <= 100_000,
        ensures
            result == -1 || 1 <= result <= k,
            result > 0 ==> repunit(result as int) % (k as int) == 0,
            result > 0 ==> forall|j: int| 1 <= j < result as int ==> repunit(j) % (k as int) != 0,
            result == -1 ==> forall|j: int| 1 <= j <= k as int ==> repunit(j) % (k as int) != 0,
    {
    }
}

}
