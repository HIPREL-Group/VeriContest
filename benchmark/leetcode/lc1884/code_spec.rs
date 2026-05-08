use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn two_egg_drop(n: i32) -> (res: i32)
        requires
            1 <= n <= 1000,
        ensures
            res >= 1,
            res * (res + 1) / 2 >= n,
            (res - 1) * res / 2 < n,
    {
        let mut n = n;
        let mut ans: i32 = 0;
        while n > 0 {
            ans += 1;
            n -= ans;
        }
        ans
    }
}

}
