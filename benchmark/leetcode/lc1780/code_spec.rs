use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sum_of_distinct_pow3(n: nat) -> bool
        decreases n,
    {
        if n == 0 {
            true
        } else {
            n % 3 != 2 && Solution::is_sum_of_distinct_pow3(n / 3)
        }
    }

    pub fn check_powers_of_three(n: i32) -> (result: bool)
        requires
            1 <= n <= 10_000_000,
        ensures
            result == Solution::is_sum_of_distinct_pow3(n as nat),
    {
        let mut cur = n;

        while cur > 0
            decreases cur,
        {
            if cur % 3 == 2 {
                return false;
            }
            cur = cur / 3;
        }
        true
    }
}

} 
