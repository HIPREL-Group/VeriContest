use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn build_number(s: int, d: int) -> int
    decreases d,
{
    if s <= 0 || d <= 0 {
        0int
    } else if d <= s {
        build_number(s - d, d - 1) * 10 + d
    } else {
        build_number(s, d - 1)
    }
}

impl Solution {
    pub fn min_varied(s: u32) -> (result: u32)
        requires
            1 <= s <= 45,
        ensures
            result as int == build_number(s as int, 9),
    {
        let mut num: u64 = 0;
        let mut mul: u64 = 1;
        let mut rem: u32 = s;
        let mut d: u32 = 9;
        while d >= 1 {
            if d <= rem {
                let new_num: u64 = num + (d as u64) * mul;
                let new_mul: u64 = mul * 10;
                let new_rem: u32 = rem - d;
                num = new_num;
                mul = new_mul;
                rem = new_rem;
            }
            d = d - 1;
        }
        num as u32
    }
}

}
