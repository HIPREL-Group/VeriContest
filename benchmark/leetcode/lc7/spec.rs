use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn reverse_spec_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let last = x % 10;
            let rest = x / 10;
            let new_acc = acc * 10 + last;
            if new_acc > u32::MAX as nat {
                0
            } else {
                Solution::reverse_spec_helper(rest, new_acc)
            }
        }
    }

    pub open spec fn reverse_spec(x: nat) -> nat {
        Solution::reverse_spec_helper(x, 0)
    }

    pub open spec fn pow_nat(base: nat, exp: nat) -> nat
        decreases exp,
    {
        if exp == 0 {
            1
        } else {
            base * Solution::pow_nat(base, (exp - 1) as nat)
        }
    }

    pub fn reverse(x: u32) -> (res: u32)
        requires
            0 <= x <= u32::MAX,
        ensures
            res == Solution::reverse_spec(x as nat),
    {
    }
}

} 
