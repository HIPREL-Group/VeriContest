use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn closest_match(cards: Seq<i32>, v: i32, end: int) -> int
    decreases end
{
    if end <= 0 {
        -1
    } else if cards[end - 1] == v {
        end - 1
    } else {
        closest_match(cards, v, end - 1)
    }
}

pub open spec fn best_pickup_upto(cards: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 {
        -1
    } else {
        let prev_best = best_pickup_upto(cards, end - 1);
        let cm = closest_match(cards, cards[end - 1], end - 1);
        let cand = if cm == -1 { -1 } else { (end - 1) - cm + 1 };
        if cand == -1 {
            prev_best
        } else if prev_best == -1 || cand < prev_best {
            cand
        } else {
            prev_best
        }
    }
}

impl Solution {
    pub fn minimum_card_pickup(cards: Vec<i32>) -> (res: i32)
        requires
            1 <= cards.len() <= 100000,
            forall|i: int| 0 <= i < cards.len() ==> 0 <= #[trigger] cards[i] <= 1000000,
        ensures
            res == -1 ==> (forall|i: int, j: int| 0 <= i < j < cards.len() as int ==> #[trigger] cards[i] != #[trigger] cards[j]),
            res != -1 ==> (exists|i: int, j: int| 0 <= i < j < cards.len() as int && #[trigger] cards[i] == #[trigger] cards[j] && res as int == j - i + 1),
            res != -1 ==> (forall|i: int, j: int| 0 <= i < j < cards.len() as int && #[trigger] cards[i] == #[trigger] cards[j] ==> res as int <= j - i + 1),
    {
        let n = cards.len();
        let mut last_seen: Vec<i32> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 1_000_000 {
            last_seen.push(-1);
            vi += 1;
        }

        let mut min_pickup: i32 = -1;
        let mut i: usize = 0;
        while i < n {
            let v = cards[i] as usize;
            let prev = last_seen[v];
            if prev != -1 {
                let cand = (i as i32) - prev + 1;
                if min_pickup == -1 || cand < min_pickup {
                    min_pickup = cand;
                }
            }
            last_seen.set(v, i as i32);
            i += 1;
        }

        min_pickup
    }
}

}
