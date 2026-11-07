use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcnt_spec_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let ones = x % 2;
            let new_acc = acc + ones;
            Solution::popcnt_spec_helper(x / 2, new_acc)
        }
    }

    pub open spec fn popcnt_spec(x: nat) -> nat {
        Solution::popcnt_spec_helper(x, 0)
    }

    pub fn hamming_weight(n: i32) -> (res: i32)
        requires
            1 <= n <= i32::MAX,
        ensures
            res == Solution::popcnt_spec(n as nat),
    {
        let mut acc: u32 = 0;
        let mut nmut = n as u32;
        while (nmut != 0) {
            acc += nmut % 2;
            nmut /= 2;
        }
        acc as i32
    }
}

} 
