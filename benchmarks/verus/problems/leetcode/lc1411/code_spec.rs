use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    pub open spec fn ways_mod(n: int, kind: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n == 1 {
            6
        } else if kind == 0 {
            (3 * Self::ways_mod(n - 1, 0) + 2 * Self::ways_mod(n - 1, 1)) % 1_000_000_007
        } else {
            (2 * Self::ways_mod(n - 1, 0) + 2 * Self::ways_mod(n - 1, 1)) % 1_000_000_007
        }
    }

    pub fn num_of_ways(n: i32) -> (res: i32)
        requires
            1 <= n <= 5000,
        ensures
            0 <= res,
            res as int == (Self::ways_mod(n as int, 0) + Self::ways_mod(n as int, 1)) % 1_000_000_007,
    {
        let modv: i64 = 1_000_000_007;
        let mut a121: i64 = 6;
        let mut a123: i64 = 6;
        let mut i: i32 = 1;
        while i < n {
            let new_a121 = (3 * a121 + 2 * a123) % modv;
            let new_a123 = (2 * a121 + 2 * a123) % modv;
            a121 = new_a121;
            a123 = new_a123;
            i = i + 1;
        }
        ((a121 + a123) % modv) as i32
    }
}

} 