use vstd::prelude::*;
use vstd::arithmetic::power::pow;

fn main() {}

verus! {

pub struct Solution;













pub open spec fn min_product_spec(p: int) -> int {
    let modulus: int = 1_000_000_007;
    let val: int = pow(2, p as nat) - 1;
    (pow(val - 1, ((val - 1) / 2) as nat) * val) % modulus
}

impl Solution {
    pub fn min_non_zero_product(p: i32) -> (result: i32)
        requires
            1 <= p <= 60,
        ensures
            result as int == min_product_spec(p as int),
    {
    }
}

} 
