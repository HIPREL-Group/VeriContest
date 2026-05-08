use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub open spec fn spec_gcd(a: nat, b: nat) -> nat
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Solution::spec_gcd(b, a % b)
        }
    }

    pub fn gcd_of_odd_even_sums(n: i32) -> (res: i32) 
        requires
            1 <= n <= 1_000,
        ensures
            res as int == Solution::spec_gcd((n * n) as nat, (n * (n - 1)) as nat) as int,
    {
        
    }

}

}
