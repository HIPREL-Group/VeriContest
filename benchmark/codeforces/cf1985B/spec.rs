use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_multiples(x: int, n: int) -> int
        recommends
            1 <= x,
            1 <= n,
    {
        let k = n / x;
        x * k * (k + 1) / 2
    }

    pub fn max_multiples_sum_x(n: i32) -> (result: i32)
        requires
            2 <= n <= 100,
        ensures
            2 <= result <= n,
            forall |x: int|
                2 <= x <= n as int ==> Self::sum_multiples(result as int, n as int)
                    >= #[trigger] Self::sum_multiples(x, n as int),
    {
    }
}

}
