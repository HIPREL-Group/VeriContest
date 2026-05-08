use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_product(n: int) -> int
        recommends
            1 <= n <= 100,
    {
        if n < 10 {
            n
        } else if n < 100 {
            (n / 10) * (n % 10)
        } else {
            0
        }
    }

    pub fn smallest_number(n: i32, t: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            1 <= t <= 10,
        ensures
            n <= result <= 100,
            Self::digit_product(result as int) % t as int == 0,
            forall|m: int| n as int <= m < result as int ==> #[trigger] (Self::digit_product(m) % t as int) != 0,
    {
    }
}

}
