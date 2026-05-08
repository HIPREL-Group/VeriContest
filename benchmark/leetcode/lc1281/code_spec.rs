use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_product_bounded(n: nat, digits: nat) -> int
    decreases digits,
{
    if digits == 0 {
        1int
    } else {
        (n % 10) as int * digit_product_bounded(n / 10, (digits - 1) as nat)
    }
}

pub open spec fn digit_sum_bounded(n: nat, digits: nat) -> int
    decreases digits,
{
    if digits == 0 {
        0int
    } else {
        (n % 10) as int + digit_sum_bounded(n / 10, (digits - 1) as nat)
    }
}

pub open spec fn digit_product(n: nat) -> int {
    digit_product_bounded(n, 6)
}

pub open spec fn digit_sum(n: nat) -> int {
    digit_sum_bounded(n, 6)
}

impl Solution {
    pub fn subtract_product_and_sum(n: i32) -> (res: i32)
        requires
            1 <= n <= 100000,
        ensures
            res == digit_product(n as nat) - digit_sum(n as nat),
    {
        let mut num: i32 = n;
        let mut product: i64 = 1;
        let mut sum: i64 = 0;
        let mut cnt: u32 = 0;

        while cnt < 6
        {
            let digit = num % 10;
            product = product * digit as i64;
            sum = sum + digit as i64;
            num = num / 10;
            cnt = cnt + 1;
        }

        (product - sum) as i32
    }
}

} 
