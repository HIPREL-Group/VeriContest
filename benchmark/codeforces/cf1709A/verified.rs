use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(v: int, x: int, a: int, b: int, c: int) -> int {
        (if x == v {
            1int
        } else {
            0
        }) + (if a == v {
            1int
        } else {
            0
        }) + (if b == v {
            1int
        } else {
            0
        }) + (if c == v {
            1int
        } else {
            0
        })
    }

    pub open spec fn key_behind(door: int, a: int, b: int, c: int) -> int {
        if door == 1 {
            a
        } else if door == 2 {
            b
        } else {
            c
        }
    }

    pub open spec fn can_open_spec(x: int, a: int, b: int, c: int) -> bool {
        if Self::key_behind(x, a, b, c) <= 0 {
            false
        } else {
            Self::key_behind(Self::key_behind(x, a, b, c), a, b, c) > 0
        }
    }

    pub fn can_open_all_doors(x: i32, a: i32, b: i32, c: i32) -> (result: bool)
        requires
            1 <= x <= 3,
            0 <= a <= 3,
            0 <= b <= 3,
            0 <= c <= 3,
            Self::count_value(1, x as int, a as int, b as int, c as int) == 1,
            Self::count_value(2, x as int, a as int, b as int, c as int) == 1,
            Self::count_value(3, x as int, a as int, b as int, c as int) == 1,
        ensures
            result == Self::can_open_spec(x as int, a as int, b as int, c as int),
    {
        let y = if x == 1 {
            a
        } else if x == 2 {
            b
        } else {
            c
        };
        if y == 0 {
            proof {
                assert(Self::key_behind(x as int, a as int, b as int, c as int) == 0);
                assert(Self::can_open_spec(x as int, a as int, b as int, c as int) == false);
            }
            false
        } else {
            let z = if y == 1 {
                a
            } else if y == 2 {
                b
            } else {
                c
            };
            proof {
                assert(x == 1 || x == 2 || x == 3);
                assert(y == Self::key_behind(x as int, a as int, b as int, c as int));
                assert(y != 0);
                assert(Self::key_behind(x as int, a as int, b as int, c as int) > 0);
                assert(z == Self::key_behind(y as int, a as int, b as int, c as int));
                if z == 0 {
                    assert(Self::can_open_spec(x as int, a as int, b as int, c as int) == false);
                } else {
                    assert(Self::can_open_spec(x as int, a as int, b as int, c as int) == true);
                }
            }
            z != 0
        }
    }
}

}
