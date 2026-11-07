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
        let mut cur: u32 = n as u32;
        let mut max1: u32 = 0;
        let mut max2: u32 = 0;

        while cur != 0
            invariant
                0 <= cur as int <= n as int,
                0 <= max2 as int <= max1 as int <= 9,
                Solution::scan_max_product(cur as nat, max1 as nat, max2 as nat)
                    == Solution::max_product_spec(n as nat),
            decreases cur,
        {
            let d: u32 = cur % 10;
            if d > max1 {
                max2 = max1;
                max1 = d;
            } else if d > max2 {
                max2 = d;
            }
            cur = cur / 10;
        }

        proof {
            assert(max1 <= 9);
            assert(max2 <= 9);
            assert(max1 * max2 <= 81) by (nonlinear_arith)
                requires
                    max1 <= 9,
                    max2 <= 9,
            {
            }
        }
        (max1 * max2) as i32
    }
}

}
