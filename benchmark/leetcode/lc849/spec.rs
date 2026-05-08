use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn is_optimal_seat(seats: Seq<i32>, pos: int, dist: int) -> bool {
    &&& seats[pos] == 0
    &&& forall |q: int| 0 <= q < seats.len() && seats[q] == 1 ==> dist <= #[trigger] abs_diff(pos, q)
    &&& exists |q: int| 0 <= q < seats.len() && seats[q] == 1 && #[trigger] abs_diff(pos, q) == dist
}

pub open spec fn seat_has_person_within(seats: Seq<i32>, pos: int, dist: int) -> bool {
    exists |q: int| 0 <= q < seats.len() && seats[q] == 1 && #[trigger] abs_diff(pos, q) <= dist
}

impl Solution {
    pub fn max_dist_to_closest(seats: Vec<i32>) -> (result: i32)
        requires
            2 <= seats.len() <= 20_000,
            forall |i: int| 0 <= i < seats.len() ==> 0 <= #[trigger] seats[i] <= 1,
            exists |i: int| 0 <= i < seats.len() && seats[i] == 0,
            exists |i: int| 0 <= i < seats.len() && seats[i] == 1,
        ensures
            1 <= result <= seats.len() - 1,
            exists |pos: int| 0 <= pos < seats.len() && is_optimal_seat(seats@, pos, result as int),
            forall |pos: int| 0 <= pos < seats.len() && seats[pos] == 0 ==> #[trigger] seat_has_person_within(seats@, pos, result as int),
    {
    }
}

}
