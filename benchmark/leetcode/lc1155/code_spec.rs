use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const MOD: i64 = 1_000_000_007;

    
    
    
    
    
    
    
    
    pub open spec fn ways(n: int, k: int, target: int) -> int
        decreases n,
    {
        if n <= 0 {
            if target == 0 { 1 } else { 0 }
        } else {
            Self::ways_sum(n, k, target, k)
        }
    }

    pub open spec fn ways_sum(n: int, k: int, target: int, f: int) -> int
        decreases n, f,
    {
        if n <= 0 || f <= 0 {
            0
        } else {
            Self::ways(n - 1, k, target - f) + Self::ways_sum(n, k, target, f - 1)
        }
    }

    pub fn num_rolls_to_target(n: i32, k: i32, target: i32) -> (result: i32)
        requires
            1 <= n <= 30,
            1 <= k <= 30,
            1 <= target <= 1000,
        ensures
            0 <= result < Self::MOD,
            result as int == Self::ways(n as int, k as int, target as int) % (Self::MOD as int),
    {
        let t = target as usize;
        let mut prev: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx <= t {
            prev.push(0i64);
            idx = idx + 1;
        }
        prev.set(0, 1i64);
        let mut die: i32 = 0;
        while die < n {
            let mut curr: Vec<i64> = Vec::new();
            let mut idx2: usize = 0;
            while idx2 <= t {
                curr.push(0i64);
                idx2 = idx2 + 1;
            }
            let mut running_sum: i64 = 0;
            let mut j: usize = 1;
            while j <= t {
                running_sum = (running_sum + prev[j - 1]) % Self::MOD;
                if j > k as usize {
                    running_sum = (running_sum - prev[j - 1 - k as usize] + Self::MOD) % Self::MOD;
                }
                curr.set(j, running_sum);
                j = j + 1;
            }
            prev = curr;
            die = die + 1;
        }
        prev[t] as i32
    }
}

} 
