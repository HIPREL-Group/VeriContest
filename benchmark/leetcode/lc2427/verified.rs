use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_factors(a: int, b: int, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            (if a % idx == 0 && b % idx == 0 { 1int } else { 0int }) + Self::count_factors(a, b, idx - 1)
        }
    }

    pub fn common_factors(a: i32, b: i32) -> (result: i32)
        requires
            1 <= a <= 1000,
            1 <= b <= 1000,
        ensures
            result == Self::count_factors(a as int, b as int, if a < b { a as int } else { b as int }),
    {
        let mut count: i32 = 0;
        let mut i: i32 = if a < b { a } else { b };
        let limit = i;
        
        while i > 0
            invariant
                1 <= a <= 1000,
                1 <= b <= 1000,
                0 <= i <= limit,
                0 <= count <= limit - i,
                limit == (if a < b { a } else { b }),
                count as int + Self::count_factors(a as int, b as int, i as int) == 
                Self::count_factors(a as int, b as int, limit as int),
            decreases i,
        {
            if a % i == 0 && b % i == 0 {
                count += 1;
            }
            i -= 1;
        }
        count
    }
}

}
