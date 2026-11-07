use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_max_product(x: nat, max1: nat, max2: nat) -> nat
        recommends
            max2 <= max1 <= 9,
        decreases x,
    {
        if x == 0 {
            max1 * max2
        } else {
            let d = x % 10;
            let rest = x / 10;
            if d > max1 {
                Solution::scan_max_product(rest, d, max1)
            } else if d > max2 {
                Solution::scan_max_product(rest, max1, d)
            } else {
                Solution::scan_max_product(rest, max1, max2)
            }
        }
    }

    pub open spec fn max_product_spec(x: nat) -> nat {
        Solution::scan_max_product(x, 0, 0)
    }

    pub fn max_product(n: i32) -> (res: i32)
        requires
            10 <= n <= 1_000_000_000,
        ensures
            res as int == Solution::max_product_spec(n as nat),
    {
    }
}

}
