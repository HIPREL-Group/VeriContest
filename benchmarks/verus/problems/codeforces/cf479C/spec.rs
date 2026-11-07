use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn lex_ordered_pair(x: (i64, i64), y: (i64, i64)) -> bool {
    x.0 < y.0 || (x.0 == y.0 && x.1 <= y.1)
}

pub open spec fn ordered_exams(exams: Seq<(i64, i64)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < exams.len() ==> #[trigger] lex_ordered_pair(exams[i], exams[j])
}

pub open spec fn valid_choice(exam: (i64, i64), day: int) -> bool {
    day == exam.0 as int || day == exam.1 as int
}

pub open spec fn ordered_day_pair(days: Seq<int>, i: int, j: int) -> bool
    recommends
        0 <= i <= j < days.len(),
{
    days[i] <= days[j]
}

pub open spec fn feasible_prefix(exams: Seq<(i64, i64)>, prefix_len: int, final_day: int) -> bool
    recommends
        1 <= prefix_len <= exams.len(),
{
    exists|days: Seq<int>|
        days.len() == prefix_len
        && days[prefix_len - 1] == final_day
        && (forall|i: int| 0 <= i < prefix_len ==> #[trigger] valid_choice(exams[i], days[i]))
        && (forall|i: int, j: int| 0 <= i <= j < prefix_len ==> #[trigger] ordered_day_pair(days, i, j))
}

impl Solution {
    pub fn min_last_exam_day(exams: Vec<(i64, i64)>) -> (result: i64)
        requires
            1 <= exams.len() <= 5000,
            ordered_exams(exams@),
            forall|i: int|
                0 <= i < exams.len() ==> 1 <= #[trigger] exams[i].1 < exams[i].0 <= 1_000_000_000,
        ensures
            feasible_prefix(exams@, exams.len() as int, result as int),
            forall|day: int|
                #[trigger] feasible_prefix(exams@, exams.len() as int, day) ==> result as int <= day,
    {
    }
}

}
