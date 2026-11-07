use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn steps_to_one(n: int) -> int
        decreases n, 
    {
        if n <= 3 {
            if n <= 1 { 0 } else { n - 1 }
        } else if n % 2 == 0 {
            1 + Self::steps_to_one(n / 2)
        } else {
            let t1 = (n + 1) / 2;
            let t2 = (n - 1) / 2;
            
            if t1 % 2 == 0 && t2 % 2 == 0 {
                2 + Self::steps_to_one(if t1 <= t2 { t1 } else { t2 })
            } else if t1 % 2 == 0 {
                2 + Self::steps_to_one(t1)
            } else {
                2 + Self::steps_to_one(t2)
            }
        }
    }

    pub fn integer_replacement(mut n: i32) -> (res: i32)
        requires
            1 <= n <= i32::MAX,
            0 <= Self::steps_to_one(n as int) < i32::MAX - 2, 
        ensures
            res == Self::steps_to_one(n as int),
    {
        
    }
}

}