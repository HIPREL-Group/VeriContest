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

    proof fn tribo_is_monotonic(i: nat, j: nat)
        requires
            i <= j,
        ensures
            Solution::tribo_spec(i) <= Solution::tribo_spec(j),
        decreases j - i,
    {
        if j < 3 {
        } else if i == j {
        } else if i == j - 1 {
        } else if i == j - 2 {
        } else {
            Solution::tribo_is_monotonic(i, (j - 1) as nat);
            Solution::tribo_is_monotonic(i, (j - 2) as nat);
            Solution::tribo_is_monotonic(i, (j - 3) as nat);
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
            invariant
                0 <= n <= 37, 
                2 <= i <= n,
                Solution::tribo_spec(n as nat) <= i32::MAX,
                prev1 == Solution::tribo_spec((i - 2) as nat),
                prev2 == Solution::tribo_spec((i - 1) as nat),
                cur == Solution::tribo_spec(i as nat),
            decreases n - i,
        {
            i = i + 1;
            proof {
                Solution::tribo_is_monotonic(i as nat, n as nat);
            }
            let new_cur = cur + prev1 + prev2;
            prev1 = prev2; 
            prev2 = cur;
            cur = new_cur;
        }
        cur
    }
}

}
