use vstd::prelude::*;
use vstd::math::{max as spec_max, min as spec_min};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn compute_area(ax1: i32, ay1: i32, ax2: i32, ay2: i32, bx1: i32, by1: i32, bx2: i32, by2: i32) -> (res: i32) 
        requires 
            -10_000 <= ax1 <= ax2 <= 10_000, 
            -10_000 <= ay1 <= ay2 <= 10_000, 
            -10_000 <= bx1 <= bx2 <= 10_000, 
            -10_000 <= by1 <= by2 <= 10_000, 
        ensures 
            res == (ax2 - ax1) * (ay2 - ay1) + (bx2 - bx1) * (by2 - by1)
                 - spec_max(0, spec_min(ax2 as int, bx2 as int) - spec_max(ax1 as int, bx1 as int)) 
                   * spec_max(0, spec_min(ay2 as int, by2 as int) - spec_max(ay1 as int, by1 as int))
    {
        
    }
}

}