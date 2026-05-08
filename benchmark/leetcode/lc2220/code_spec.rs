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

    pub fn min_bit_flips(start: i32, goal: i32) -> (res: i32)
        requires
            0 <= start <= i32::MAX,
            0 <= goal <= i32::MAX,
        ensures
            res == Solution::popcnt_spec((start ^ goal) as nat),
    {
        let mut xor = (start ^ goal) as u32;
        let mut count: u32 = 0;
        while xor != 0 {
            count += xor % 2;
            xor /= 2;
        }
        count as i32
    }
}

} 
