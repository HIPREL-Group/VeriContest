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
        let num: u64 = x as u64;
        let mut i: u64 = 0;
        let mut j: u64 = num;
        let mut found: bool = false; 

        while i <= j && !found
        {
            let mid = (i + j) / 2;
            let tmp = mid * mid;

            if tmp == num {
                found = true;
            } else if tmp > num {
                j = mid - 1;
            } else {
                i = mid + 1;
            }
        }

        ((i + j) / 2) as i32
    }
}

}