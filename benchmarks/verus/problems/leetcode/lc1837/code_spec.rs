use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_div_decreases;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_sum_base(n: nat, k: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % k) + digit_sum_base(n / k, k)
    }
}


impl Solution {
    pub fn sum_base(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            2 <= k <= 10,
        ensures
            result == digit_sum_base(n as nat, k as nat) as i32,
    {
        let mut sum: i32 = 0;
        let mut cur: i32 = n;
        while cur > 0 {
            sum = sum + cur % k;
            cur = cur / k;
        }
        sum
    }
}

} 
