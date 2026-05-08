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
        
    }
}

}