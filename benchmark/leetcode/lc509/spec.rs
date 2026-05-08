use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fib_spec(n: nat) -> nat
        decreases n
    {
        if n <= 0 { 
            0 
        } else if n == 1 { 
            1 
        } else { 
            Solution::fib_spec((n - 2) as nat) + Solution::fib_spec((n - 1) as nat) 
        }
    }

    pub fn fib(n: i32) -> (res: i32) 
        requires 
            0 <= n <= 30, 
            Solution::fib_spec(n as nat) <= i32::MAX, 
        ensures 
            res == Solution::fib_spec(n as nat), 
    {
        
    }
}

}
