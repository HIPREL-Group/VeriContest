use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn step_digit(x: int, delta: int) -> int {
    ((x + delta) % 10 + 10) % 10
}

pub open spec fn apply_moves_from(x: int, deltas: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        x
    } else {
        apply_moves_from(step_digit(x, deltas[lo] as int), deltas, lo + 1, hi)
    }
}

impl Solution {
    pub fn recover_digit(final_d: i32, move_deltas: Vec<i32>) -> (res: i32)
        requires
            0 <= final_d <= 9,
            move_deltas.len() <= 10,
            forall|j: int|
                0 <= j < move_deltas.len() ==> #[trigger] move_deltas[j] == 1 || move_deltas[j] == -1,
        ensures
            0 <= res <= 9,
            apply_moves_from(res as int, move_deltas@, 0, move_deltas.len() as int) == final_d as int,
            forall|x: int|
                0 <= x <= 9 && #[trigger] apply_moves_from(x, move_deltas@, 0, move_deltas.len() as int) == final_d as int
                    ==> x == res as int,
    {
    }
}

}
