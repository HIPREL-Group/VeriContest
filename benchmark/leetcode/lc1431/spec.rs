use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn kids_with_candies(candies: Vec<i32>, extra_candies: i32) -> (result: Vec<bool>)
        requires
            2 <= candies.len() <= 100,
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 100,
            1 <= extra_candies <= 50,
        ensures
            result.len() == candies.len(),
            forall |i: int| 0 <= i < candies.len() ==>
                #[trigger] result[i] ==
                    (forall |j: int| 0 <= j < candies.len() ==> candies[i] + extra_candies >= candies[j]),
    {
    }
}

}