use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn diff_spec(n: int, m: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            (if n % m == 0 { -n } else { n }) + Self::diff_spec(n - 1, m)
        }
    }

    pub fn difference_of_sums(n: i32, m: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            1 <= m <= 1000,
        ensures
            result == Self::diff_spec(n as int, m as int),
    {
        let mut diff: i32 = 0;
        let mut i: i32 = n;
        
        while i > 0
        {
            if i % m == 0 {
                diff -= i;
            } else {
                diff += i;
            }
            i -= 1;
        }
        diff
    }
}

}
