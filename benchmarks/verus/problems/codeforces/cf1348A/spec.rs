use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn pow2_int(e: int) -> int
    decreases e,
{
    if e <= 0 {
        1
    } else {
        2 * pow2_int(e - 1)
    }
}

pub open spec fn min_balance_answer(n: int) -> int {
    pow2_int(n / 2 + 1) - 2
}

pub struct Solution;

impl Solution {
    pub fn phoenix_balance_min_diff(n: i32) -> (result: i64)
        requires
            2 <= n <= 30,
            (n as int) % 2 == 0,
        ensures
            result as int == min_balance_answer(n as int),
            exists|e: int|
                e == (n as int) / 2 + 1 && result as int == #[trigger] pow2_int(e) - 2,
    {
    }
}

}
