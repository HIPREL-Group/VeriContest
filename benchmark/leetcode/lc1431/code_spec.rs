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
        let n = candies.len();
        let mut max_candies = candies[0];
        let mut max_index: usize = 0;
        let mut i: usize = 1;

        while i < n {
            if candies[i] > max_candies {
                max_candies = candies[i];
                max_index = i;
            }
            i = i + 1;
        }

        let threshold = candies[max_index] - extra_candies;
        let mut result: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            let can_have_most = candies[k] >= threshold;
            result.push(can_have_most);
            k = k + 1;
        }

        result
    }
}

}