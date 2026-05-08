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

    pub open spec fn num_digits(x: nat) -> nat
        decreases x,
    {
        if x == 0 {
            0
        } else {
            1 + Solution::num_digits(x / 10)
        }
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
        let mut res: u32 = 0;
        let mut cur: u32 = x;

        while cur != 0
            invariant
                0 <= cur <= x,
                Solution::reverse_spec_helper(cur as nat, res as nat) == Solution::reverse_spec(
                    x as nat,
                ),
            decreases cur,
        {
            match res.checked_mul(10) {
                None => return 0,
                Some(tmp) => match tmp.checked_add(cur % 10) {
                    None => return 0,
                    Some(fine) => {
                        res = fine;
                    },
                },
            }
            cur = cur / 10;
        }

        res
    }
}

} 
