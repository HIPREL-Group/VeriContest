use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn bulb_switch(n: i32) -> (res: i32)
        requires
            0 <= n <= 1_000_000_000,
        ensures
            res >= 0,
            res * res <= n,
            (res + 1) * (res + 1) > n,
    {
        let mut i: i32 = 0;
        loop
        {
            if (i as i64 + 1) * (i as i64 + 1) > n as i64 {
                break;
            }
            i += 1;
        }
        i
    }
}

}
