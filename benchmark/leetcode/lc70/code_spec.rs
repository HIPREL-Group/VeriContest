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

    pub fn climb_stairs(n: i32) -> (res: i32) 
        requires 
            1 <= n <= 45, 
            Solution::fib_spec((n + 1) as nat) <= i32::MAX, 
        ensures 
            res == Solution::fib_spec((n + 1) as nat), 
    {
        let mut prev: i32 = 0;
        let mut cur: i32 = 1;
        let mut i: i32 = 1;
        while i <= n
        {
            i = i + 1;
            let new_cur = cur + prev;
            prev = cur;
            cur = new_cur;
        }
        cur
    }
}

}
