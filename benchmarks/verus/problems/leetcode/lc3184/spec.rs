use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inner_count(hours: Seq<i32>, i: int, j: int) -> int
        decreases hours.len() - j,
    {
        if j >= hours.len() {
            0
        } else {
            (if (hours[i] as int + hours[j] as int) % 24 == 0 { 1int } else { 0int })
                + Self::inner_count(hours, i, j + 1)
        }
    }

    pub open spec fn pair_count(hours: Seq<i32>, i: int) -> int
        decreases hours.len() - i,
    {
        if i >= hours.len() {
            0
        } else {
            Self::inner_count(hours, i, i + 1) + Self::pair_count(hours, i + 1)
        }
    }

    pub fn count_complete_day_pairs(hours: Vec<i32>) -> (res: i32)
        requires
            1 <= hours.len() <= 100,
            forall|i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
        ensures
            res as int == Self::pair_count(hours@, 0),
            0 <= res <= hours.len() * hours.len(),
    {
    }
}

}
