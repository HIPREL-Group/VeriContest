use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn get_bit(x: i32, i: u32) -> bool
        recommends
            0 <= i < 32,
    {
        (x >> i) & 1 == 1
    }

    pub fn reverse_bits(n: i32) -> (res: i32)
        requires
            0 <= n <= 2_147_483_646,
            n % 2 == 0,
        ensures
            forall|i: int|
                0 <= i < 32 ==> #[trigger] Solution::get_bit(res, i as u32) == Solution::get_bit(
                    n,
                    (31 - i) as u32,
                ),
    {
        let (mut res, mut x) = (0i32, n);

        let mut i: u32 = 0;
        while i < 32 {
            let new_res = (res << 1) | (x & 1);
            let new_x = x >> 1;
            res = new_res;
            x = new_x;
            i += 1;
        }
        res
    }
}

} 
