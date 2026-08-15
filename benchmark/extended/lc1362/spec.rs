use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_pair(a: int, b: int, num: int) -> bool {
    a >= 1 && b >= 1 && (a * b == num + 1 || a * b == num + 2)
}

pub open spec fn pair_diff(a: int, b: int) -> int {
    b - a
}

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

impl Solution {
    pub fn closest_divisors(num: i32) -> (res: Vec<i32>)
        requires
            1 <= num <= 1_000_000_000,
        ensures
            res.len() == 2,
            res[0] >= 1 && res[1] >= 1,
            is_valid_pair(res[0] as int, res[1] as int, num as int),
            forall|a: int, b: int|
                1 <= a <= b && (a * b == (num as int) + 1 || a * b == (num as int) + 2) ==>
                    abs_diff(res[0] as int, res[1] as int) <= #[trigger] pair_diff(a, b),
    {
    }
}

}
