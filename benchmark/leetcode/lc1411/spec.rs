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
    }
}

} 