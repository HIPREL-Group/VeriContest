use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn stirling_mod(n: int, k: int) -> int
    decreases n
{
    if k < 0 || k > n || n < 0 {
        0
    } else if n == k {
        1
    } else if k == 0 {
        0
    } else {
        (stirling_mod(n - 1, k - 1) + ((n - 1) * stirling_mod(n - 1, k)) % 1_000_000_007) % 1_000_000_007
    }
}

impl Solution {
    pub fn rearrange_sticks(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            1 <= k <= n,
        ensures
            result == stirling_mod(n as int, k as int) as i32,
    {
        let modp: i64 = 1_000_000_007;
        let nn = n as usize;
        let kk = k as usize;
        let mut prev: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx <= kk {
            prev.push(0i64);
            idx += 1;
        }
        prev.set(0, 1i64);
        let mut i: usize = 1;
        while i <= nn {
            let mut curr: Vec<i64> = Vec::new();
            let mut idx2: usize = 0;
            while idx2 <= kk {
                curr.push(0i64);
                idx2 += 1;
            }
            let max_j: usize = if i < kk { i } else { kk };
            let mut j: usize = 1;
            while j <= max_j {
                let term1: i64 = prev[j - 1];
                let term2: i64 = ((i as i64 - 1) * prev[j]) % modp;
                let val: i64 = (term1 + term2) % modp;
                curr.set(j, val);
                j += 1;
            }
            prev = curr;
            i += 1;
        }
        prev[kk] as i32
    }
}

}
