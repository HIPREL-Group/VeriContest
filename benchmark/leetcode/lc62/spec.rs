use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn unique_paths_spec(m: nat, n: nat) -> nat
        decreases m + n
    {
        if m == 0 || n == 0 {
            0
        } else if m == 1 || n == 1 {
            1
        } else {
            Solution::unique_paths_spec((m - 1) as nat, n)
                + Solution::unique_paths_spec(m, (n - 1) as nat)
        }
    }

    pub fn unique_paths(m: i32, n: i32) -> (result: i32)
        requires
            1 <= m <= 100,
            1 <= n <= 100,
            Solution::unique_paths_spec(m as nat, n as nat) <= i32::MAX,
        ensures
            result == Solution::unique_paths_spec(m as nat, n as nat),
    {
    }
}

} 
