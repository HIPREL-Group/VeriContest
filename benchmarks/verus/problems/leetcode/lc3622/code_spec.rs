use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    pub open spec fn digit_product(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else {
            (n % 10) * Self::digit_product(n / 10)
        }
    }

    pub open spec fn check_divisibility_spec(n: nat) -> bool {
        let d = Self::digit_sum(n) + Self::digit_product(n);
        d > 0 && n % d == 0
    }

    fn digit_sum_exec(x: u32) -> (sum: u32)
        requires
            x <= 1_000_000,
        ensures
            sum as nat == Self::digit_sum(x as nat),
            sum <= x,
            x > 0 ==> sum > 0,
    {
        if x == 0 {
            0
        } else {
            let d = x % 10;
            let q = x / 10;
            let s = Self::digit_sum_exec(q);
            if q == 0 {
                d
            } else {
                d + s
            }
        }
    }

    fn digit_product_exec(x: u32) -> (prod: u32)
        requires
            x <= 1_000_000,
        ensures
            prod as nat == Self::digit_product(x as nat),
            x == 0 ==> prod == 1,
            x > 0 ==> prod <= x,
    {
        if x == 0 {
            1
        } else {
            let d = x % 10;
            let q = x / 10;
            let p = Self::digit_product_exec(q);
            if q == 0 {
                d
            } else {
                d * p
            }
        }
    }

    pub fn check_divisibility(n: i32) -> (result: bool)
        requires
            1 <= n <= 1_000_000,
        ensures
            result == Self::check_divisibility_spec(n as nat),
    {
        let x = n as u32;
        let s = Self::digit_sum_exec(x);
        let p = Self::digit_product_exec(x);
        let denom = s + p;
        x % denom == 0
    }
}

}
