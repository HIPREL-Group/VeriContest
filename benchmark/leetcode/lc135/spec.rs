use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_spec(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            s[start] as int + Self::sum_spec(s, start + 1, end)
        }
    }

    pub fn candy(ratings: Vec<i32>) -> (result: i32)
        requires
            1 <= ratings.len() <= 20_000,
            forall|i: int| 0 <= i < ratings.len() ==> 0 <= #[trigger] ratings[i] <= 20_000,
        ensures
            exists|candies: Seq<i32>|
                {
                    &&& candies.len() == ratings.len()
                    &&& (forall|i: int|
                        0 <= i < candies.len() ==> #[trigger] candies[i] >= 1)
                    &&& (forall|i: int|
                        0 < i < ratings.len() && ratings[i] > ratings[i - 1] ==> #[trigger] candies[i]
                            > candies[i - 1])
                    &&& (forall|i: int|
                        0 <= i < ratings.len() - 1 && ratings[i] > ratings[i + 1] ==> #[trigger] candies[i]
                            > candies[i + 1])
                    &&& result == Self::sum_spec(candies, 0, candies.len() as int)
                },
            result >= ratings.len(),
    {
    }
}

}
