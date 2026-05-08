use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn longest_string_spec(x: int, y: int, z: int) -> int {
        (Self::min2(x, y + 1) + Self::min2(x + 1, y) + z) * 2
    }

    pub fn longest_string(x: i32, y: i32, z: i32) -> (result: i32)
        requires
            1 <= x <= 50,
            1 <= y <= 50,
            1 <= z <= 50,
        ensures
            result as int == Self::longest_string_spec(x as int, y as int, z as int),
    {
    }
}

}
