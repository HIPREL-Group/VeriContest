use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn colored_until(i: nat) -> int
    recommends
        i >= 1,
{
    1 + 2 * i as int * (i as int - 1)
}

impl Solution {
    pub fn colored_cells(n: i32) -> (result: i64)
        requires
            1 <= n <= 100000,
        ensures
            result as int == colored_until(n as nat),
    {
        let mut ans: i128 = 1;
        let mut i: i128 = 1;

        while i < n as i128 {
            ans = ans + 4 * i;
            i = i + 1;
        }

        ans as i64
    }
}

}
