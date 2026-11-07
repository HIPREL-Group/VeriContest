use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_reverse_inner(n: nat, acc: nat) -> nat
        decreases n
    {
        if n == 0 {
            acc
        } else {
            Self::spec_reverse_inner(n / 10, (acc * 10 + (n % 10)) as nat)
        }
    }

    pub open spec fn spec_reverse(n: nat) -> nat {
        Self::spec_reverse_inner(n, 0)
    }

    pub fn is_same_after_reversals(num: i32) -> (res: bool) 
        requires 
            0 <= num <= 1_000_000, 
        ensures
            res == (Self::spec_reverse(Self::spec_reverse(num as nat)) == num as nat)
    {
        let mut n = num;
        let mut reversed1 = 0i32;
        
        while n > 0
        {
            reversed1 = reversed1 * 10 + n % 10;
            n = n / 10;
        }
        
        let mut m = reversed1;
        let mut reversed2 = 0i32;
        
        while m > 0
        {
            reversed2 = reversed2 * 10 + m % 10;
            m = m / 10;
        }
        
        reversed2 == num
    }
}

}