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

    fn min2_exec(a: i32, b: i32) -> (res: i32)
        ensures
            res as int == Self::min2(a as int, b as int),
    {
        if a <= b { a } else { b }
    }

    pub fn longest_string(x: i32, y: i32, z: i32) -> (result: i32)
        requires
            1 <= x <= 50,
            1 <= y <= 50,
            1 <= z <= 50,
        ensures
            result as int == Self::longest_string_spec(x as int, y as int, z as int),
    {
        proof {
            assert((x as int) + 1 <= 51);
            assert((y as int) + 1 <= 51);
            assert(0 <= Self::min2(x as int, (y as int) + 1) <= 50);
            assert(0 <= Self::min2((x as int) + 1, y as int) <= 50);
            assert(
                (Self::min2(x as int, (y as int) + 1)
                    + Self::min2((x as int) + 1, y as int)
                    + (z as int)) * 2 <= 304
            );
        }
        (Self::min2_exec(x, y + 1) + Self::min2_exec(x + 1, y) + z) * 2
    }
}

}
