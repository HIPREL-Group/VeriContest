use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_k(rating: Seq<i32>, i: int, j: int, k: int) -> int
        recommends
            0 <= i < j < k <= rating.len(),
        decreases if k > j { k - j } else { 0int },
    {
        if k <= j + 1 {
            0
        } else {
            Self::count_k(rating, i, j, k - 1) + 
            (if (rating[i] < rating[j] && rating[j] < rating[k - 1]) || 
                (rating[i] > rating[j] && rating[j] > rating[k - 1]) { 1int } else { 0int })
        }
    }

    pub open spec fn count_j(rating: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i < j <= rating.len(),
        decreases if j > i { j - i } else { 0int },
    {
        if j <= i + 1 {
            0
        } else {
            Self::count_j(rating, i, j - 1) + Self::count_k(rating, i, j - 1, rating.len() as int)
        }
    }

    pub open spec fn count_i(rating: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= rating.len(),
        decreases if i > 0 { i } else { 0int },
    {
        if i <= 0 {
            0
        } else {
            Self::count_i(rating, i - 1) + Self::count_j(rating, i - 1, rating.len() as int)
        }
    }

    pub fn num_teams(rating: Vec<i32>) -> (result: i32)
        requires
            3 <= rating.len() <= 1000,
            forall|x: int| 0 <= x < rating.len() ==> 1 <= #[trigger] rating[x] <= 100000,
        ensures
            result == Self::count_i(rating@, rating.len() as int),
    {
    }
}

}
