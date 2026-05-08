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
        proof {
            assert(valid_pt(coordinates[0]@));
            assert(valid_pt(coordinates[1]@));
        }
        let x0 = coordinates[0][0];
        let y0 = coordinates[0][1];
        let x1 = coordinates[1][0];
        let y1 = coordinates[1][1];
        let dx = x1 - x0;
        let dy = y1 - y0;
        
        let mut i = 2;
        
        while i < coordinates.len()
            invariant
                2 <= i <= coordinates.len(),
                x0 == coordinates[0][0],
                y0 == coordinates[0][1],
                x1 == coordinates[1][0],
                y1 == coordinates[1][1],
                dx == coordinates[1][0] - coordinates[0][0],
                dy == coordinates[1][1] - coordinates[0][1],
                forall |k: int| #![trigger coordinates[k]] 0 <= k < coordinates.len() ==> valid_pt(coordinates[k]@),
                forall |k: int| #![trigger coordinates[k]] 2 <= k < i ==> 
                    (coordinates[1][1] - coordinates[0][1]) as int * (coordinates[k][0] - coordinates[0][0]) as int == 
                    (coordinates[k][1] - coordinates[0][1]) as int * (coordinates[1][0] - coordinates[0][0]) as int,
            decreases coordinates.len() - i
        {
            proof {
                assert(valid_pt(coordinates[i as int]@));
            }
            let xi = coordinates[i][0];
            let yi = coordinates[i][1];
            
            proof {
                assert(-20000 <= dx <= 20000);
                assert(-20000 <= dy <= 20000);
                assert(-20000 <= xi - x0 <= 20000);
                assert(-20000 <= yi - y0 <= 20000);
                assert(-400_000_000 <= (dy as int) * ((xi - x0) as int) <= 400_000_000) by (nonlinear_arith)
                    requires
                        -20000 <= dy <= 20000,
                        -20000 <= xi - x0 <= 20000;
                assert(-400_000_000 <= ((yi - y0) as int) * (dx as int) <= 400_000_000) by (nonlinear_arith)
                    requires
                        -20000 <= yi - y0 <= 20000,
                        -20000 <= dx <= 20000;
            }
            
            if (dy as i64) * ((xi - x0) as i64) != ((yi - y0) as i64) * (dx as i64) {
                assert(((coordinates[1][1] - coordinates[0][1]) as int * (coordinates[i as int][0] - coordinates[0][0]) as int) != 
                       ((coordinates[i as int][1] - coordinates[0][1]) as int * (coordinates[1][0] - coordinates[0][0]) as int));
                return false;
            }
            
            i += 1;
        }
        
        true
    }
}

}
