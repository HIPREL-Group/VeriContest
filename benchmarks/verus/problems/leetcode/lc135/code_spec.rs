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

    pub open spec fn valid_dist(ratings: Seq<i32>, candies: Seq<i32>) -> bool {
        &&& candies.len() == ratings.len()
        &&& (forall|i: int| #![trigger candies[i]] 0 <= i < candies.len() ==> candies[i] >= 1)
        &&& (forall|i: int|
            #![trigger candies[i], candies[i - 1]]
            0 < i < ratings.len() && ratings[i] > ratings[i - 1] ==> candies[i] > candies[i - 1])
        &&& (forall|i: int|
            #![trigger candies[i], candies[i + 1]]
            0 <= i < ratings.len() - 1 && ratings[i] > ratings[i + 1] ==> candies[i] > candies[i
                + 1])
    }

    pub fn candy(ratings: Vec<i32>) -> (result: i32)
        requires
            1 <= ratings.len() <= 20_000,
            forall|i: int| 0 <= i < ratings.len() ==> 0 <= #[trigger] ratings[i] <= 20_000,
        ensures
            exists|candies: Seq<i32>|
                Self::valid_dist(ratings@, candies) && result == #[trigger] Self::sum_spec(
                    candies,
                    0,
                    candies.len() as int,
                ),
            forall|candies: Seq<i32>|
                #[trigger] Self::valid_dist(ratings@, candies) ==> result <= Self::sum_spec(
                    candies,
                    0,
                    candies.len() as int,
                ),
            result >= ratings.len(),
    {
        let n = ratings.len();

        let mut left: Vec<i32> = Vec::new();
        left.push(1i32);
        let mut i: usize = 1;
        while i < n {
            if ratings[i] > ratings[i - 1] {
                let v = left[i - 1] + 1;
                left.push(v);
            } else {
                left.push(1i32);
            }
            i += 1;
        }

        let mut right: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            right.push(1i32);
            i += 1;
        }

        if n >= 2 {
            let mut idx: usize = n - 1;
            while idx > 0 {
                idx -= 1;
                if ratings[idx] > ratings[idx + 1] {
                    let v = right[idx + 1] + 1;
                    right.set(idx, v);
                }
            }
        }

        let mut candy: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            let c = if left[i] > right[i] { left[i] } else { right[i] };
            candy.push(c);
            i += 1;
        }

        let mut total: i32 = 0;
        i = 0;
        while i < n {
            total += candy[i];
            i += 1;
        }

        total
    }
}

}