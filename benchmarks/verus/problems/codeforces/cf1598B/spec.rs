use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn student_can_attend(days: Seq<Vec<bool>>, i: int, d: int) -> bool {
    days[i]@[d]
}

pub open spec fn count_can_attend_one(days: Seq<Vec<bool>>, d: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else { count_can_attend_one(days, d, end - 1) + (if student_can_attend(days, end - 1, d) { 1int } else { 0int }) }
}

pub open spec fn count_can_attend_either(days: Seq<Vec<bool>>, d1: int, d2: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else { count_can_attend_either(days, d1, d2, end - 1) + (if student_can_attend(days, end - 1, d1) || student_can_attend(days, end - 1, d2) { 1int } else { 0int }) }
}

pub open spec fn is_valid_pair(n: usize, days: Seq<Vec<bool>>, d1: int, d2: int) -> bool {
    0 <= d1 && d1 < d2 && d2 < 5 &&
    count_can_attend_either(days, d1, d2, n as int) == n as int &&
    count_can_attend_one(days, d1, n as int) >= (n / 2) as int &&
    count_can_attend_one(days, d2, n as int) >= (n / 2) as int
}

pub open spec fn has_valid_pair(n: usize, days: Seq<Vec<bool>>) -> bool {
    exists|d1: int, d2: int| is_valid_pair(n, days, d1, d2)
}

pub struct Solution;

impl Solution {
    pub fn groups(n: usize, days: Vec<Vec<bool>>) -> (res: bool)
        requires
            2 <= n && n <= 1000,
            n % 2 == 0,
            days.len() == n,
            forall|i: int| 0 <= i && i < n ==> days@[i].len() == 5,
            forall|i: int| 0 <= i && i < n ==>
                days@[i]@[0] || days@[i]@[1] || days@[i]@[2] || days@[i]@[3] || days@[i]@[4],
        ensures
            res == has_valid_pair(n, days@)
    {
    }
}

}
