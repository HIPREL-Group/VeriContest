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

    proof fn fib_is_monotonic(i: nat, j: nat)
        requires
            i <= j,
        ensures
            Solution::fib_spec(i) <= Solution::fib_spec(j),
        decreases j - i,
    {
        if j < 2 {
        } else if i == j {
        } else if i == j - 1 {
        } else {
            Solution::fib_is_monotonic(i, (j - 1) as nat);
            Solution::fib_is_monotonic(i, (j - 2) as nat);
        }
    }

    pub fn fib(n: i32) -> (res: i32) 
        requires 
            0 <= n <= 30, 
            Solution::fib_spec(n as nat) <= i32::MAX, 
        ensures 
            res == Solution::fib_spec(n as nat), 
    {
        if n == 0 {
            return 0;
        }
        let mut prev: i32 = 0;
        let mut cur: i32 = 1;
        let mut i: i32 = 1;
        while i < n
            invariant
                0 < i <= n,
                Solution::fib_spec(n as nat) <= i32::MAX,
                cur == Solution::fib_spec(i as nat),
                prev == Solution::fib_spec((i - 1) as nat),
            decreases n - i,
        {
            i = i + 1;
            proof {
                Solution::fib_is_monotonic(i as nat, n as nat);
            }
            let new_cur = cur + prev;
            prev = cur;
            cur = new_cur;
        }
        cur
    }
}

}
