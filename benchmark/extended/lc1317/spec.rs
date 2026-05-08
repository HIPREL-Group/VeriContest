use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_no_zero(x: int) -> bool
        decreases x,
    {
        if x <= 0 {
            false
        } else if x < 10 {
            true
        } else {
            x % 10 != 0 && Solution::is_no_zero(x / 10)
        }
    }

    pub fn get_no_zero_integers(n: i32) -> (result: Vec<i32>)
        requires
            2 <= n <= 10000,
        ensures
            result@.len() == 2,
            1 <= result@[0] && 1 <= result@[1],
            result@[0] + result@[1] == n,
            Solution::is_no_zero(result@[0] as int),
            Solution::is_no_zero(result@[1] as int),
    {
    }
}

} 
