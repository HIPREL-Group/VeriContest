use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_spec(start: i32, idx: int) -> i32
        decreases idx,
    {
        if idx <= 0 { 0i32 }
        else { Self::xor_spec(start, idx - 1) ^ ((start as int + 2 * (idx - 1)) as i32) }
    }

    pub fn xor_operation(n: i32, start: i32) -> (result: i32)
        requires 
            1 <= n <= 1000, 
            0 <= start <= 1000,
        ensures 
            result == Self::xor_spec(start, n as int),
    {
        let mut ans: i32 = 0;
        let mut i: i32 = 0;
        while i < n
            invariant
                1 <= n <= 1000,
                0 <= start <= 1000,
                0 <= i <= n,
                ans == Self::xor_spec(start, i as int),
            decreases n - i,
        {
            ans ^= start + 2 * i;
            i += 1;
        }
        ans
    }
}

}
