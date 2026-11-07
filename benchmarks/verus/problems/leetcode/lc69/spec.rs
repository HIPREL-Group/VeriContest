use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn my_sqrt(x: i32) -> (res: i32) 
        requires 
            0 <= x <= i32::MAX, 
        ensures 
            (res as int) * (res as int) <= x as int
                && ((res as int) + 1) * ((res as int) + 1) > x as int,
    {
        
    }
}

}