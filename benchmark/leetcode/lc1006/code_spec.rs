use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn clumsy_rest(m: int) -> int
        decreases m,
    {
        if m <= 0 { 0 }
        else if m == 1 { 1 }
        else if m == 2 { m * (m - 1) }
        else if m == 3 { m * (m - 1) / (m - 2) }
        else { m * (m - 1) / (m - 2) - (m - 3) + Solution::clumsy_rest(m - 4) }
    }

    pub open spec fn clumsy_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else if n == 1 { 1 }
        else if n == 2 { n * (n - 1) }
        else if n == 3 { n * (n - 1) / (n - 2) }
        else { n * (n - 1) / (n - 2) + (n - 3) - Solution::clumsy_rest(n - 4) }
    }

    pub fn clumsy(n: i32) -> (result: i32)
        requires
            1 <= n <= 10000,
        ensures
            result as int == Solution::clumsy_spec(n as int),
    {
        if n == 1 { return 1; }
        if n == 2 { return 2; }
        if n == 3 { return 6; }

        let mut result = n * (n - 1) / (n - 2) + (n - 3);
        let mut k = n - 4;

        while k >= 4 {
            result = result - k * (k - 1) / (k - 2) + (k - 3);
            k = k - 4;
        }

        if k == 3 {
            result = result - k * (k - 1) / (k - 2);
        } else if k == 2 {
            result = result - k * (k - 1);
        } else if k == 1 {
            result = result - k;
        }

        result
    }
}

} 
