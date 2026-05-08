use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_valid_k(n: int, k: int) -> bool {
        k >= 1 && n - k * (k - 1) / 2 > 0 && (n - k * (k - 1) / 2) % k == 0
    }

    pub open spec fn count_ways(n: int, bound: int) -> nat
        decreases bound,
    {
        if bound <= 0 {
            0
        } else {
            Self::count_ways(n, bound - 1) + if Self::is_valid_k(n, bound) { 1 as nat } else { 0 as nat }
        }
    }

    pub fn consecutive_numbers_sum(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result as int == Self::count_ways(n as int, n as int),
    {
        let n64: i64 = n as i64;
        let mut count: i32 = 0;
        let mut k: i64 = 1;
        let mut sum: i64 = 0;
        while sum < n64 {
            let r: i64 = (n64 - sum) % k;
            if r == 0 {
                count = count + 1;
            }
            sum = sum + k;
            k = k + 1;
        }
        count
    }
}

} 