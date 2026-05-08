use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn arrange_coins(n: i32) -> (res: i32) 
        requires
            1 <= n <= i32::MAX, 
        ensures 
            res * (res + 1) / 2 <= n < (res + 1) * (res + 2) / 2, 
    {
        let mut step: i32 = 0;
        let mut remaining: i32 = n;
        
        while remaining > step && step < 65535
        {
            step = step + 1;
            remaining = remaining - step;
        }
        
        step
    }
}

}