use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tribo_spec(n: nat) -> nat
        decreases n
    {
        if n <= 0 { 
            0 
        } else if n == 1 { 
            1 
        } else if n == 2 {
            1
        } else { 
            Solution::tribo_spec((n - 3) as nat) + Solution::tribo_spec((n - 2) as nat) + Solution::tribo_spec((n - 1) as nat) 
        }
    }

    pub fn tribonacci(n: i32) -> (res: i32) 
        requires 
            0 <= n <= 37, 
            Solution::tribo_spec(n as nat) <= i32::MAX, 
        ensures 
            res == Solution::tribo_spec(n as nat), 
    {
        
    }
}

}
