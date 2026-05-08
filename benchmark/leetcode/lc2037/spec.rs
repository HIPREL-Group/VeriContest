use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_prefix(s: Seq<i32>, p: int, len: int) -> int
        recommends
            0 <= len <= s.len(),
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            Self::count_prefix(s, p, len - 1) + if s[len - 1] == p as i32 { 1int } else { 0int }
        }
    }

    pub open spec fn count_value(s: Seq<i32>, p: int) -> int {
        Self::count_prefix(s, p, s.len() as int)
    }

    pub open spec fn abs_int(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn moves_from(pos: int, balance: int, seats: Seq<i32>, students: Seq<i32>) -> int
        decreases if pos <= 100 { 101 - pos } else { 0int },
    {
        if pos > 100 {
            0
        } else {
            let next_balance = balance + Self::count_value(seats, pos) - Self::count_value(students, pos);
            Self::abs_int(next_balance) + Self::moves_from(pos + 1, next_balance, seats, students)
        }
    }

    pub fn min_moves_to_seat(seats: Vec<i32>, students: Vec<i32>) -> (result: i32)
        requires
            1 <= seats.len() <= 100,
            students.len() == seats.len(),
            seats@.len() <= 100,
            students@.len() == seats@.len(),
            forall |i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 100,
            forall |i: int| 0 <= i < students.len() ==> 1 <= #[trigger] students[i] <= 100,
        ensures
            result as int == Self::moves_from(1, 0, seats@, students@),
    {
    }
}

}
