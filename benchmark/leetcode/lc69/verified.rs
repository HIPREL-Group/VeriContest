use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn my_sqrt(x: i32) -> (res: i32) 
        requires 
            0 <= x <= i32::MAX, 
        ensures 
            (res as int) * (res as int) <= x as int
                && ((res as int) + 1) * ((res as int) + 1) > x as int,
    {
        let num: u64 = x as u64;
        let mut i: u64 = 0;
        let mut j: u64 = num;
        let mut found: bool = false; 

        assert((j + 1) * (j + 1) > num) by(nonlinear_arith)
            requires
                j == num, 
                num <= i32::MAX,
        {}

        while i <= j && !found
            invariant 
                num == x as u64,
                0 <= num <= i32::MAX, 
                0 <= i <= num + 1,
                0 <= j <= num,
                i > 0 ==> (i - 1) * (i - 1) <= num,
                (j + 1) * (j + 1) > num,
                i > j ==> i == j + 1,
                found ==> ((i + j) / 2) * ((i + j) / 2) == num, 
                found ==> ((i + j) / 2 + 1) * ((i + j) / 2 + 1) > num,
        {
            let mid = (i + j) / 2;
            
            assert(mid * mid <= u64::MAX) by(nonlinear_arith)
                requires
                    mid <= i32::MAX,
            {}

            let tmp = mid * mid;

            if tmp == num {
                found = true;
                assert((mid + 1) * (mid + 1) > num) by(nonlinear_arith)
                    requires
                        mid * mid == num,
                        mid <= i32::MAX,
                {}
            } else if tmp > num {
                assert(mid >= 1) by(nonlinear_arith)
                    requires
                        mid * mid > num,
                        num >= 0,
                {}
                j = mid - 1;
            } else {
                i = mid + 1;
            }
        }

        ((i + j) / 2) as i32
    }
}

}