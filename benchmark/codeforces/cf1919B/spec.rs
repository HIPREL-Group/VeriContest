use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn min_penalty(plus_count: i64, minus_count: i64) -> (result: i64)
        requires
            0 <= plus_count <= 5000,
            0 <= minus_count <= 5000,
        ensures
            result == if plus_count >= minus_count { plus_count - minus_count } else { minus_count - plus_count },
    {
    }
}

}
