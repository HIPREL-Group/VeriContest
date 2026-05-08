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
        let m = m as usize;
        let n = n as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            dp.push(1i32);
            k += 1;
        }
        let mut i: usize = 1;
        while i < m {
            let mut j: usize = 1;
            while j < n {
                let dpj: i32 = dp[j];
                let dpjm1: i32 = dp[j - 1];
                dp.set(j, dpj + dpjm1);
                j += 1;
            }
            i += 1;
        }
        dp[n - 1]
    }
}

} 
