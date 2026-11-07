use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn catalan(n: int) -> int {
        if n == 0 { 1 }
        else if n == 1 { 1 }
        else if n == 2 { 2 }
        else if n == 3 { 5 }
        else if n == 4 { 14 }
        else if n == 5 { 42 }
        else if n == 6 { 132 }
        else if n == 7 { 429 }
        else if n == 8 { 1430 }
        else if n == 9 { 4862 }
        else if n == 10 { 16796 }
        else if n == 11 { 58786 }
        else if n == 12 { 208012 }
        else if n == 13 { 742900 }
        else if n == 14 { 2674440 }
        else if n == 15 { 9694845 }
        else if n == 16 { 35357670 }
        else if n == 17 { 129644790 }
        else if n == 18 { 477638700 }
        else if n == 19 { 1767263190 }
        else { 0 }
    }

    pub open spec fn catalan_partial_sum(n: int, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Solution::catalan(k - 1) * Solution::catalan(n - k)
                + Solution::catalan_partial_sum(n, k - 1)
        }
    }

    pub fn num_trees(n: i32) -> (result: i32)
        requires
            1 <= n <= 19,
        ensures
            result as int == Solution::catalan(n as int),
    {
        let mut dp: Vec<i32> = Vec::new();
        dp.push(1i32);
        dp.push(1i32);
        let mut i: usize = 2;
        while i <= n as usize {
            let mut sum: i32 = 0;
            let mut j: usize = 0;
            while j < i {
                let dj = dp[j];
                let dimj = dp[i - 1 - j];
                sum = sum + dj * dimj;
                j = j + 1;
            }
            dp.push(sum);
            i = i + 1;
        }
        dp[n as usize]
    }
}

} 
