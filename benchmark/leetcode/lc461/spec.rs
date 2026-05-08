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

    pub fn hamming_distance(x: i32, y: i32) -> (res: i32)
        requires
            0 <= x <= i32::MAX,
            0 <= y <= i32::MAX,
        ensures
            res == Solution::popcnt_spec((x ^ y) as nat),
    {
    }
}

} 
