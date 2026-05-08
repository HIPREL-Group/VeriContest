use vstd::prelude::*;
use vstd::math::{max as spec_max, min as spec_min};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn max(x: i64, y: i64) -> (res: i64)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        
    }

    pub fn min(x: i64, y: i64) -> (res: i64)
        ensures (res as int) == spec_min(x as int, y as int)
    {
        
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
        
    }
}

}