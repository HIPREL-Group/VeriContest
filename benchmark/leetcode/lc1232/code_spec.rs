use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_pt(p: Seq<i32>) -> bool {
    p.len() == 2 && -10000 <= p[0] && p[0] <= 10000 && -10000 <= p[1] && p[1] <= 10000
}

impl Solution {
    pub fn check_straight_line(coordinates: Vec<Vec<i32>>) -> (result: bool)
        requires
            2 <= coordinates.len() <= 1000,
            forall |i: int| #![trigger coordinates[i]] 0 <= i < coordinates.len() ==> valid_pt(coordinates[i]@),
        ensures
            result <==> forall |k: int| #![trigger coordinates[k]] 2 <= k < coordinates.len() ==> 
                (coordinates[1][1] - coordinates[0][1]) as int * (coordinates[k][0] - coordinates[0][0]) as int == 
                (coordinates[k][1] - coordinates[0][1]) as int * (coordinates[1][0] - coordinates[0][0]) as int,
    {
        let x0 = coordinates[0][0];
        let y0 = coordinates[0][1];
        let x1 = coordinates[1][0];
        let y1 = coordinates[1][1];
        let dx = x1 - x0;
        let dy = y1 - y0;
        
        let mut i = 2;
        while i < coordinates.len() 
        {
            let xi = coordinates[i][0];
            let yi = coordinates[i][1];
            if (dy as i64) * ((xi - x0) as i64) != ((yi - y0) as i64) * (dx as i64) {
                return false;
            }
            i += 1;
        }
        
        true
    }
}

}
