use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_odd(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_odd(s, end - 1) + if s[end - 1] % 2 != 0 { 1int } else { 0int }
        }
    }

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub fn min_cost_to_move_chips(position: Vec<i32>) -> (res: i32)
        requires
            1 <= position.len() <= 100,
            forall |i: int| 0 <= i < position.len() ==> 1 <= #[trigger] position[i] <= 1_000_000_000,
        ensures
            res as int == Self::spec_min(
                Self::count_odd(position@, position.len() as int),
                position.len() as int - Self::count_odd(position@, position.len() as int),
            ),
    {

    }
}

}
