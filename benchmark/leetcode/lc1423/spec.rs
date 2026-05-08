use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(cards: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 0 { 0 }
        else { Self::prefix_sum(cards, n - 1) + cards[n - 1] as int }
    }

    pub open spec fn suffix_sum(cards: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 0 { 0 }
        else { Self::suffix_sum(cards, n - 1) + cards[cards.len() - n] as int }
    }

    pub open spec fn max_score_spec(cards: Seq<i32>, k: int, i: int) -> int
        decreases k - i + 1
    {
        if i > k { 0 }
        else {
            let score = Self::prefix_sum(cards, i) + Self::suffix_sum(cards, k - i);
            let rest = Self::max_score_spec(cards, k, i + 1);
            if score >= rest { score } else { rest }
        }
    }
    
    pub fn max_score(card_points: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= card_points.len(),
            card_points.len() <= 100_000,
            forall |i: int| 0 <= i < card_points.len() ==> 1 <= #[trigger] card_points[i] <= 10_000,
            1 <= k,
            k <= card_points.len(),
        ensures
            res as int == Self::max_score_spec(card_points@, k as int, 0),
    {
    }
}

}
