use vstd::prelude::*;
use vstd::math::{max as spec_max, min as spec_min};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn max(x: i64, y: i64) -> (res: i64)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        if x >= y { x } else { y }
    }

    pub fn min(x: i64, y: i64) -> (res: i64)
        ensures (res as int) == spec_min(x as int, y as int)
    {
        if x <= y { x } else { y }
    }

    pub fn largest_square_area(bl: Vec<Vec<i32>>, tr: Vec<Vec<i32>>) -> (res: i64)
        requires
            bl.len() == tr.len(),
            2 <= bl.len() <= 1_000, 
            forall|i: int| 0 <= i < bl.len() ==> bl[i].len() == 2,
            forall|i: int| 0 <= i < tr.len() ==> tr[i].len() == 2,
            forall|i: int| 0 <= i < bl.len() ==> 
                bl[i][0] < tr[i][0] && bl[i][1] < tr[i][1],
            forall|i: int| 0 <= i < bl.len() ==> 
                0 <= #[trigger] bl[i][0] <= 10_000_000 &&
                0 <= #[trigger] bl[i][1] <= 10_000_000 &&
                0 <= #[trigger] tr[i][0] <= 10_000_000 &&
                0 <= #[trigger] tr[i][1] <= 10_000_000,
        ensures
            res >= 0,
            res > 0 ==> exists|i: int, j: int| 
                0 <= i < bl.len() && i < j < bl.len() &&
                !(bl[j][0] as i64 >= tr[i][0] as i64 || 
                  tr[j][0] as i64 <= bl[i][0] as i64 || 
                  bl[j][1] as i64 >= tr[i][1] as i64 || 
                  tr[j][1] as i64 <= bl[i][1] as i64) &&
                spec_min(
                    spec_min(tr[i][0] as int, tr[j][0] as int) - spec_max(bl[i][0] as int, bl[j][0] as int),
                    spec_min(tr[i][1] as int, tr[j][1] as int) - spec_max(bl[i][1] as int, bl[j][1] as int)
                ) * spec_min(
                    spec_min(tr[i][0] as int, tr[j][0] as int) - spec_max(bl[i][0] as int, bl[j][0] as int),
                    spec_min(tr[i][1] as int, tr[j][1] as int) - spec_max(bl[i][1] as int, bl[j][1] as int)
                ) == res,
            forall|i: int, j: int| 
                (0 <= i < bl.len() && i < j < bl.len() &&
                 !(bl[j][0] as i64 >= tr[i][0] as i64 || 
                   tr[j][0] as i64 <= bl[i][0] as i64 || 
                   bl[j][1] as i64 >= tr[i][1] as i64 || 
                   tr[j][1] as i64 <= bl[i][1] as i64)) ==> 
                spec_min(
                    spec_min(tr[i][0] as int, tr[j][0] as int) - spec_max(bl[i][0] as int, bl[j][0] as int),
                    spec_min(tr[i][1] as int, tr[j][1] as int) - spec_max(bl[i][1] as int, bl[j][1] as int)
                ) * spec_min(
                    spec_min(tr[i][0] as int, tr[j][0] as int) - spec_max(bl[i][0] as int, bl[j][0] as int),
                    spec_min(tr[i][1] as int, tr[j][1] as int) - spec_max(bl[i][1] as int, bl[j][1] as int)
                ) <= res,
    {
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        
        while i < bl.len()
        {
            let x1 = bl[i][0] as i64;
            let y1 = bl[i][1] as i64;
            let x2 = tr[i][0] as i64;
            let y2 = tr[i][1] as i64;
            
            let mut j: usize = i + 1;
            
            while j < bl.len()
            {
                let a1 = bl[j][0] as i64;
                let b1 = bl[j][1] as i64;
                let a2 = tr[j][0] as i64;
                let b2 = tr[j][1] as i64;
                
                if !(a1 >= x2 || a2 <= x1 || b1 >= y2 || b2 <= y1) {
                    let ix1 = Self::max(x1, a1);
                    let iy1 = Self::max(y1, b1);
                    let ix2 = Self::min(x2, a2);
                    let iy2 = Self::min(y2, b2);
                    let side = Self::min(ix2 - ix1, iy2 - iy1);
                    
                    let area = side * side;
                    
                    if area > ans {
                        ans = area;
                    }
                }
                
                j += 1;
            }
            
            i += 1;
        }
        
        ans
    }
}

}