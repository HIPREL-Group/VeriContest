use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn arrange_coins(n: i32) -> (res: i32) 
        requires
            1 <= n <= i32::MAX, 
        ensures 
            res * (res + 1) / 2 <= n < (res + 1) * (res + 2) / 2, 
    {
        let mut step: i32 = 0;
        let mut remaining: i32 = n;
        
        while remaining > step && step < 65535
            invariant
                1 <= n <= i32::MAX,
                0 <= step <= 65535,
                remaining == n - step * (step + 1) / 2,
                0 <= remaining <= n,
            decreases remaining,
        {
            step = step + 1;
            remaining = remaining - step;
            
            assert(remaining == n - step * (step + 1) / 2) by {
                assert(step * (step + 1) == (step - 1) * step + 2 * step) by(nonlinear_arith);
            };
        }
        
        assert(n < (step + 1) * (step + 2) / 2) by {
            if remaining <= step {
                assert(step * (step + 1) == step * step + step) by(nonlinear_arith);
                assert((step + 1) * (step + 2) == step * step + 3 * step + 2) by(nonlinear_arith);
            } 
        };
        
        step
    }
}

}