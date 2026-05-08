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

    proof fn unique_paths_mono_rows(a: nat, c: nat, n: nat)
        requires
            1 <= a,
            1 <= n,
            a <= c,
        ensures
            Solution::unique_paths_spec(a, n) <= Solution::unique_paths_spec(c, n),
        decreases c - a,
    {
        if c == a {
        } else if n == 1 {
        } else {
            Solution::unique_paths_mono_rows(a, (c - 1) as nat, n);
            assert(Solution::unique_paths_spec(c, n)
                == Solution::unique_paths_spec((c - 1) as nat, n)
                    + Solution::unique_paths_spec(c, (n - 1) as nat));
        }
    }

    proof fn unique_paths_mono_cols(m: nat, b: nat, d: nat)
        requires
            1 <= m,
            1 <= b,
            b <= d,
        ensures
            Solution::unique_paths_spec(m, b) <= Solution::unique_paths_spec(m, d),
        decreases d - b,
    {
        if d == b {
        } else if m == 1 {
        } else {
            Solution::unique_paths_mono_cols(m, b, (d - 1) as nat);
            assert(Solution::unique_paths_spec(m, d)
                == Solution::unique_paths_spec((m - 1) as nat, d)
                    + Solution::unique_paths_spec(m, (d - 1) as nat));
        }
    }

    proof fn unique_paths_mono(a: nat, b: nat, c: nat, d: nat)
        requires
            1 <= a,
            1 <= b,
            a <= c,
            b <= d,
        ensures
            Solution::unique_paths_spec(a, b) <= Solution::unique_paths_spec(c, d),
    {
        Solution::unique_paths_mono_rows(a, c, b);
        Solution::unique_paths_mono_cols(c, b, d);
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
        while k < n
            invariant
                k <= n,
                dp.len() == k,
                forall |j: int| #![auto] 0 <= j < k ==> dp[j] == 1i32,
            decreases n - k,
        {
            dp.push(1i32);
            k += 1;
        }
        proof {
            assert forall |k: int| 0 <= k < n implies
                dp[k] as int == Solution::unique_paths_spec(1nat, (k + 1) as nat) as int
            by {
                assert(Solution::unique_paths_spec(1nat, (k + 1) as nat) == 1nat);
            };
        }
        let mut i: usize = 1;
        while i < m
            invariant
                1 <= m <= 100,
                1 <= n <= 100,
                1 <= i,
                i <= m,
                dp.len() == n,
                Solution::unique_paths_spec(m as nat, n as nat) <= i32::MAX,
                forall |k: int| #![auto] 0 <= k < n ==>
                    dp[k] as int == Solution::unique_paths_spec(i as nat, (k + 1) as nat) as int,
            decreases m - i,
        {
            proof {
                let k0: int = 0;
                assert(dp[k0] as int == Solution::unique_paths_spec(i as nat, (k0 + 1) as nat) as int);
                assert(Solution::unique_paths_spec(i as nat, 1nat) == 1nat);
                assert(Solution::unique_paths_spec((i + 1) as nat, 1nat) == 1nat);
            }
            let mut j: usize = 1;
            while j < n
                invariant
                    1 <= m <= 100,
                    1 <= n <= 100,
                    1 <= i,
                    i < m,
                    1 <= j,
                    j <= n,
                    dp.len() == n,
                    Solution::unique_paths_spec(m as nat, n as nat) <= i32::MAX,
                    forall |k: int| #![auto] 0 <= k < j ==>
                        dp[k] as int == Solution::unique_paths_spec((i + 1) as nat, (k + 1) as nat) as int,
                    forall |k: int| #![auto] j <= k < n ==>
                        dp[k] as int == Solution::unique_paths_spec(i as nat, (k + 1) as nat) as int,
                decreases n - j,
            {
                let dpj: i32 = dp[j];
                let dpjm1: i32 = dp[j - 1];
                proof {
                    assert(dpj as int == Solution::unique_paths_spec(i as nat, (j as int + 1) as nat) as int);
                    assert(dpjm1 as int == Solution::unique_paths_spec((i + 1) as nat, j as nat) as int);
                    assert(Solution::unique_paths_spec((i + 1) as nat, (j as int + 1) as nat)
                        == Solution::unique_paths_spec(i as nat, (j as int + 1) as nat)
                            + Solution::unique_paths_spec((i + 1) as nat, j as nat));
                    Solution::unique_paths_mono(
                        (i + 1) as nat, (j as int + 1) as nat,
                        m as nat, n as nat,
                    );
                    assert(dpj as int + dpjm1 as int <= i32::MAX as int);
                }
                dp.set(j, dpj + dpjm1);
                j += 1;
            }
            i += 1;
        }
        proof {
            let kn: int = n as int - 1;
            assert(dp[kn] as int == Solution::unique_paths_spec(i as nat, (kn + 1) as nat) as int);
        }
        dp[n - 1]
    }
}

} 
