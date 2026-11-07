use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rounds(x: int, y: int) -> int {
        if x <= y / 4 { x } else { y / 4 }
    }

    pub fn winning_player(x: i32, y: i32) -> (result: String)
        requires
            1 <= x <= 100,
            1 <= y <= 100,
        ensures
            result@ == if Self::rounds(x as int, y as int) % 2 == 1 {
                "Alice"@
            } else {
                "Bob"@
            },
    {
    }
}

}
