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

proof fn lemma_closest_match_char(cards: Seq<i32>, v: i32, end: int)
    requires 0 <= end <= cards.len(),
    ensures
        closest_match(cards, v, end) == -1 ==> (forall |k: int| 0 <= k < end ==> #[trigger] cards[k] != v),
        (forall |k: int| 0 <= k < end ==> #[trigger] cards[k] != v) ==> closest_match(cards, v, end) == -1,
        closest_match(cards, v, end) != -1 ==> (
            0 <= closest_match(cards, v, end) < end
            && cards[closest_match(cards, v, end)] == v
            && (forall |k: int| closest_match(cards, v, end) < k < end ==> #[trigger] cards[k] != v)
        ),
    decreases end
{
    if end > 0 {
        lemma_closest_match_char(cards, v, end - 1);
    }
}

proof fn lemma_best_pickup_char(cards: Seq<i32>, end: int)
    requires 0 <= end <= cards.len(),
    ensures
        best_pickup_upto(cards, end) == -1 ==>
            (forall |i: int, j: int| 0 <= i < j < end ==> #[trigger] cards[i] != #[trigger] cards[j]),
        (forall |i: int, j: int| 0 <= i < j < end ==> #[trigger] cards[i] != #[trigger] cards[j]) ==>
            best_pickup_upto(cards, end) == -1,
        best_pickup_upto(cards, end) != -1 ==> (
            exists |i: int, j: int| 0 <= i < j < end && #[trigger] cards[i] == #[trigger] cards[j]
                && best_pickup_upto(cards, end) == j - i + 1
        ),
        best_pickup_upto(cards, end) != -1 ==> (
            forall |i: int, j: int| 0 <= i < j < end && #[trigger] cards[i] == #[trigger] cards[j]
                ==> best_pickup_upto(cards, end) <= j - i + 1
        ),
    decreases end
{
    if end > 0 {
        lemma_best_pickup_char(cards, end - 1);
        lemma_closest_match_char(cards, cards[end - 1], end - 1);
        let prev_best = best_pickup_upto(cards, end - 1);
        let cm = closest_match(cards, cards[end - 1], end - 1);
        let cand = if cm == -1 { -1int } else { (end - 1) - cm + 1 };
        if cm == -1 {
            assert(forall |k: int| 0 <= k < end - 1 ==> #[trigger] cards[k] != cards[end - 1]);
        } else {
            assert(cards[cm] == cards[end - 1]);
            assert(forall |k: int| cm < k < end - 1 ==> #[trigger] cards[k] != cards[end - 1]);
            assert forall |k: int| 0 <= k < end - 1 && #[trigger] cards[k] == cards[end - 1] implies k <= cm by {
                if k > cm {
                    assert(cards[k] != cards[end - 1]);
                }
            }
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
        while vi <= 1_000_000
            invariant
                last_seen@.len() == vi as int,
                0 <= vi <= 1_000_001,
                forall |v: int| 0 <= v < vi as int ==> #[trigger] last_seen@[v] == closest_match(cards@, v as i32, 0),
            decreases 1_000_001 - vi,
        {
            last_seen.push(-1);
            vi += 1;
        }

        let mut min_pickup: i32 = -1;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == cards.len(),
                1 <= cards.len() <= 100000,
                last_seen@.len() == 1_000_001,
                forall |k: int| 0 <= k < cards.len() ==> 0 <= #[trigger] cards@[k] <= 1_000_000,
                forall |v: int| 0 <= v <= 1_000_000 ==> #[trigger] last_seen@[v] == closest_match(cards@, v as i32, i as int),
                min_pickup as int == best_pickup_upto(cards@, i as int),
                -1 <= min_pickup <= 100_000,
            decreases n - i,
        {
            let v = cards[i] as usize;
            proof {
                assert(cards@[i as int] as int == v as int);
            }
            let prev = last_seen[v];
            proof {
                assert(prev as int == closest_match(cards@, cards@[i as int], i as int));
                lemma_closest_match_char(cards@, cards@[i as int], i as int);
                if prev != -1 {
                    assert(0 <= prev < n as i32);
                }
            }
            if prev != -1 {
                let cand = (i as i32) - prev + 1;
                if min_pickup == -1 || cand < min_pickup {
                    min_pickup = cand;
                }
            }
            proof {
                assert forall |vv: int| 0 <= vv <= 1_000_000 && vv != v as int implies
                    #[trigger] last_seen@[vv] == closest_match(cards@, vv as i32, i as int + 1) by {
                    assert(cards@[i as int] as int != vv);
                }
            }
            last_seen.set(v, i as i32);
            i += 1;
        }

        proof {
            lemma_best_pickup_char(cards@, n as int);
        }
        min_pickup
    }
}

}
