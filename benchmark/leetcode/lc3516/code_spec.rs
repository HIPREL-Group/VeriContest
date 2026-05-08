use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn distance(a: int, b: int) -> int {
        if a >= b {
            a - b
        } else {
            b - a
        }
    }

    pub fn find_closest(x: i32, y: i32, z: i32) -> (result: i32)
        requires
            1 <= x <= 100,
            1 <= y <= 100,
            1 <= z <= 100,
        ensures
            result as int
                == if Self::distance(x as int, z as int) < Self::distance(y as int, z as int) {
                    1int
                } else if Self::distance(y as int, z as int) < Self::distance(x as int, z as int) {
                    2int
                } else {
                    0int
                },
    {
        let dx = if x >= z {
            x - z
        } else {
            z - x
        };
        let dy = if y >= z {
            y - z
        } else {
            z - y
        };
        if dx < dy {
            1
        } else if dy < dx {
            2
        } else {
            0
        }
    }
}

}
