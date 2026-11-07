use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn merge_triplets(triplets: Vec<Vec<i32>>, target: Vec<i32>) -> (res: bool)
        requires
            1 <= triplets.len() <= 100_000,
            target.len() == 3,
            forall |i: int| 0 <= i < triplets.len() ==> #[trigger] triplets[i].len() == 3,
            forall |i: int, j: int| 0 <= i < triplets.len() && 0 <= j < triplets[i].len() ==> 1 <= #[trigger] triplets[i][j] <= 1000,
            forall |j: int| 0 <= j < 3 ==> 1 <= #[trigger] target[j] <= 1000,
        ensures
            res == (
                (exists |i: int|
                    0 <= i < triplets.len()
                    && triplets[i].len() == 3
                    && triplets[i][0] == target[0]
                    && triplets[i][1] <= target[1]
                    && triplets[i][2] <= target[2]
                )
                && (exists |i: int|
                    0 <= i < triplets.len()
                    && triplets[i].len() == 3
                    && triplets[i][0] <= target[0]
                    && triplets[i][1] == target[1]
                    && triplets[i][2] <= target[2]
                )
                && (exists |i: int|
                    0 <= i < triplets.len()
                    && triplets[i].len() == 3
                    && triplets[i][0] <= target[0]
                    && triplets[i][1] <= target[1]
                    && triplets[i][2] == target[2]
                )
            ),
    {
    }
}

}