use vstd::prelude::*;
use vstd::math::{max as spec_max, min as spec_min};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn max(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        if x >= y { x as i32 } else { y as i32 }
    }

    pub fn min(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_min(x as int, y as int)
    {
        if x <= y { x as i32} else { y as i32 }
    }

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
        assert((ax2 - ax1) * (ay2 - ay1) <= 400_000_000) by(nonlinear_arith)
            requires 
                -10_000 <= ax1 <= ax2 <= 10_000, 
                -10_000 <= ay1 <= ay2 <= 10_000, 
        {}

        assert((bx2 - bx1) * (by2 - by1) <= 400_000_000) by(nonlinear_arith)
            requires 
                -10_000 <= bx1 <= bx2 <= 10_000, 
                -10_000 <= by1 <= by2 <= 10_000, 
        {}

        let area1 = (ax2 - ax1) * (ay2 - ay1);
        let area2 = (bx2 - bx1) * (by2 - by1);
        let overlap_x = Self::max(0, Self::min(ax2, bx2) - Self::max(ax1, bx1));
        let overlap_y = Self::max(0, Self::min(ay2, by2) - Self::max(ay1, by1));
        
        assert(0 <= overlap_x <= 20_000);
        assert(0 <= overlap_y <= 20_000);
        
        assert(overlap_x * overlap_y <= 400_000_000) by(nonlinear_arith)
            requires 
                0 <= overlap_x <= 20_000,
                0 <= overlap_y <= 20_000,
        {}
        
        let intersection = overlap_x * overlap_y;
        
        assert(area1 + area2 - intersection <= 800_000_000) by(nonlinear_arith)
            requires
                area1 <= 400_000_000,
                area2 <= 400_000_000,
                intersection >= 0,
        {}
        
        return area1 + area2 - intersection;
    }
}

}