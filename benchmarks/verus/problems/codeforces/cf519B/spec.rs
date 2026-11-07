use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_errors_valid(s: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000
}

pub open spec fn count_value(s: Seq<i64>, value: i64) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == value { 1int } else { 0int }) + count_value(s.subrange(1, s.len() as int), value)
    }
}

pub open spec fn single_deletion(from: Seq<i64>, to: Seq<i64>, deleted: i64) -> bool {
    from.len() == to.len() + 1
        && forall|v: i64| #[trigger] count_value(from, v) == count_value(to, v) + if v == deleted { 1int } else { 0int }
}

impl Solution {
    pub fn find_compilation_errors(first: Vec<i64>, second: Vec<i64>, third: Vec<i64>) -> (result: (i64, i64))
        requires
            3 <= first.len() <= 100_000,
            all_errors_valid(first@),
            all_errors_valid(second@),
            all_errors_valid(third@),
            exists|x: i64| single_deletion(first@, second@, x),
            exists|y: i64| single_deletion(second@, third@, y),
        ensures
            single_deletion(first@, second@, result.0),
            single_deletion(second@, third@, result.1),
    {
    }
}

}
