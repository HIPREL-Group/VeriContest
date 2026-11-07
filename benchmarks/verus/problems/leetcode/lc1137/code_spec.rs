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
        if n == 0 {
            return 0;
        }
        else if n == 1 {
            return 1;
        }
        let mut prev1: i32 = 0;
        let mut prev2: i32 = 1;
        let mut cur: i32 = 1;

        let mut i: i32 = 2;
        while i < n
        {
            i = i + 1;
            let new_cur = cur + prev1 + prev2;
            prev1 = prev2; 
            prev2 = cur;
            cur = new_cur;
        }
        cur
    }
}

}
