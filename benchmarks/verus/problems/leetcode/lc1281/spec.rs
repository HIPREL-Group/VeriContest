use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_product(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1int
    } else {
        (n % 10) as int * digit_product((n / 10) as nat)
    }
}

pub open spec fn digit_sum(n: nat) -> int
    decreases n,
{
    if n == 0 {
        0int
    } else {
        (n % 10) as int + digit_sum((n / 10) as nat)
    }
}

impl Solution {
    pub fn subtract_product_and_sum(n: i32) -> (res: i32)
        requires
            1 <= n <= 100000,
        ensures
            res == digit_product(n as nat) - digit_sum(n as nat),
    {
    }
}

}