use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_min_value(s: Seq<i64>, m: int) -> bool {
    &&& s.len() > 0
    &&& exists|j: int| 0 <= j < s.len() && s[j] as int == m
    &&& forall|j: int| 0 <= j < s.len() ==> m <= s[j] as int
}

pub open spec fn sum_decrease_with(s: Seq<i64>, end: int, m: int) -> int
    recommends
        0 <= end <= s.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        sum_decrease_with(s, end - 1, m) + (s[end - 1] as int - m)
    }
}

impl Solution {
    pub fn min_operations_to_equal(candies: Vec<i64>) -> (result: i64)
        requires
            1 <= candies.len() <= 50,
            forall|i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] as int <= 1_000_000_000,
        ensures
            exists|min_v: int| is_min_value(candies@, min_v)
                && result as int == sum_decrease_with(candies@, candies.len() as int, min_v),
    {
    }
}

}
