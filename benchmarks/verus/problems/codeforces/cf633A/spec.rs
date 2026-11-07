use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn exact_damage_feasible(a: int, b: int, c: int) -> bool {
    exists|x: int, y: int| x >= 0 && y >= 0 && #[trigger] (a * x + b * y) == c
}

impl Solution {
    pub fn exact_damage_possible(a: i32, b: i32, c: i32) -> (res: bool)
        requires
            1 <= a <= 100,
            1 <= b <= 100,
            1 <= c <= 10_000,
        ensures
            res == exact_damage_feasible(a as int, b as int, c as int),
    {
    }
}

}
