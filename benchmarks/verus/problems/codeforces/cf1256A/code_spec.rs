use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn can_pay_exact(a: int, b: int, n: int, S: int) -> bool {
        exists|x: int, y: int|
            0 <= x <= a && 0 <= y <= b && #[trigger] (x * n + y) == S
    }

    pub fn payment_without_change(a: i64, b: i64, n: i64, S: i64) -> (res: bool)
        requires
            1 <= a <= 1000000000,
            1 <= b <= 1000000000,
            1 <= n <= 1000000000,
            1 <= S <= 1000000000,
        ensures
            res == Self::can_pay_exact(a as int, b as int, n as int, S as int),
    {
        let x = if a < S / n {
            a
        } else {
            S / n
        };
        let rem = S - x * n;
        rem <= b
    }
}

}
