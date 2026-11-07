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

    fn check_no_zero(x: i32) -> (result: bool)
        requires
            0 <= x <= 10000,
        ensures
            result == Solution::is_no_zero(x as int),
    {
        if x <= 0 {
            return false;
        }
        let mut val = x;
        while val >= 10 {
            if val % 10 == 0 {
                return false;
            }
            val = val / 10;
        }
        true
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
        let mut a: i32 = 1;
        while a < n {
            let b = n - a;
            if Self::check_no_zero(a) && Self::check_no_zero(b) {
                let mut res = Vec::new();
                res.push(a);
                res.push(b);
                return res;
            }
            a = a + 1;
        }
        let mut res = Vec::new();
        res.push(1);
        res.push(n - 1);
        res
    }
}

} 
