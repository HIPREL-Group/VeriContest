use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn reverse_checked_spec_helper(x: nat, acc: nat) -> int
        decreases x,
    {
        if x == 0 {
            acc as int
        } else {
            let next = acc * 10 + x % 10;
            if next > i32::MAX as nat {
                -1
            } else {
                Solution::reverse_checked_spec_helper(x / 10, next)
            }
        }
    }

    pub open spec fn reverse_checked_spec(x: nat) -> int {
        Solution::reverse_checked_spec_helper(x, 0)
    }

    pub open spec fn mirror_distance_spec(n: int) -> int {
        let r = Solution::reverse_checked_spec(n as nat);
        if r == -1 {
            n
        } else if n >= r {
            n - r
        } else {
            r - n
        }
    }

    pub fn mirror_distance(n: i32) -> (res: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            res as int == Solution::mirror_distance_spec(n as int),
    {
    }
}

} 
