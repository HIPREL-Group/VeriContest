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

    proof fn lemma_prefix_sum_bounds(cards: Seq<i32>, n: int)
        requires
            0 <= n <= cards.len(),
            forall |i: int| 0 <= i < cards.len() ==> 1 <= #[trigger] cards[i] <= 10_000,
        ensures
            Self::prefix_sum(cards, n) >= 0,
            Self::prefix_sum(cards, n) <= n * 10_000,
        decreases n
    {
        if n > 0 {
            Self::lemma_prefix_sum_bounds(cards, n - 1);
        }
    }

    proof fn lemma_suffix_sum_bounds(cards: Seq<i32>, n: int)
        requires
            0 <= n <= cards.len(),
            forall |i: int| 0 <= i < cards.len() ==> 1 <= #[trigger] cards[i] <= 10_000,
        ensures
            Self::suffix_sum(cards, n) >= 0,
            Self::suffix_sum(cards, n) <= n * 10_000,
        decreases n
    {
        if n > 0 {
            Self::lemma_suffix_sum_bounds(cards, n - 1);
        }
    }

    proof fn lemma_max_score_spec_unfold(cards: Seq<i32>, k: int, m: int)
        requires
            0 <= m <= k,
            0 <= k <= cards.len(),
            forall |i: int| 0 <= i < cards.len() ==> 1 <= #[trigger] cards[i] <= 10_000,
        ensures
            Self::max_score_spec(cards, k, m) ==
                (if Self::prefix_sum(cards, m) + Self::suffix_sum(cards, k - m) >=
                    Self::max_score_spec(cards, k, m + 1)
                {
                    Self::prefix_sum(cards, m) + Self::suffix_sum(cards, k - m)
                } else {
                    Self::max_score_spec(cards, k, m + 1)
                }),
    {
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
        let n = card_points.len();
        let k = k as usize;
        let mut left_sum = 0i32;
        let mut right_sum = 0i32;
        let mut i = 0usize;
        while i < k
            invariant
                0 <= i <= k,
                k <= n,
                n == card_points.len(),
                n <= 100_000,
                left_sum as int == Self::prefix_sum(card_points@, i as int),
                0 <= left_sum as int,
                left_sum as int <= i * 10_000,
                forall |j: int| 0 <= j < card_points.len() ==> 1 <= #[trigger] card_points[j] <= 10_000,
            decreases k - i
        {
            proof {
                Self::lemma_prefix_sum_bounds(card_points@, i as int);
                assert(Self::prefix_sum(card_points@, i as int + 1) ==
                    Self::prefix_sum(card_points@, i as int) + card_points@[i as int] as int);
            }
            left_sum = left_sum + card_points[i];
            i = i + 1;
        }

        let mut best = left_sum;
        proof {
            assert(Self::suffix_sum(card_points@, 0int) == 0);
            Self::lemma_prefix_sum_bounds(card_points@, k as int);
            assert(Self::max_score_spec(card_points@, k as int, k as int) ==
                Self::prefix_sum(card_points@, k as int) + Self::suffix_sum(card_points@, 0int)) by {
                assert(Self::max_score_spec(card_points@, k as int, k as int) ==
                    (if Self::prefix_sum(card_points@, k as int) + Self::suffix_sum(card_points@, k as int - k as int) >=
                        Self::max_score_spec(card_points@, k as int, k as int + 1)
                    {
                        Self::prefix_sum(card_points@, k as int) + Self::suffix_sum(card_points@, k as int - k as int)
                    } else {
                        Self::max_score_spec(card_points@, k as int, k as int + 1)
                    }));
                assert(Self::max_score_spec(card_points@, k as int, k as int + 1) == 0int);
                assert(Self::suffix_sum(card_points@, k as int - k as int) == Self::suffix_sum(card_points@, 0int));
                Self::lemma_prefix_sum_bounds(card_points@, k as int);
            }
        }

        let mut i = 0usize;
        while i < k
            invariant
                0 <= i <= k,
                k <= n,
                n == card_points.len(),
                n <= 100_000,
                left_sum as int == Self::prefix_sum(card_points@, (k - i) as int),
                right_sum as int == Self::suffix_sum(card_points@, i as int),
                best as int == Self::max_score_spec(card_points@, k as int, (k - i) as int),
                0 <= left_sum as int,
                left_sum as int <= (k - i) * 10_000,
                0 <= right_sum as int,
                right_sum as int <= i * 10_000,
                0 <= best as int,
                best as int <= k * 10_000,
                forall |j: int| 0 <= j < card_points.len() ==> 1 <= #[trigger] card_points[j] <= 10_000,
            decreases k - i
        {
            let left_card_idx = k - 1 - i;
            let right_card_idx = n - 1 - i;

            proof {
                assert(Self::prefix_sum(card_points@, (k - i) as int) ==
                    Self::prefix_sum(card_points@, (k - i - 1) as int) +
                    card_points@[(k - i - 1) as int] as int);
                assert(Self::suffix_sum(card_points@, (i + 1) as int) ==
                    Self::suffix_sum(card_points@, i as int) +
                    card_points@[(card_points@.len() - (i + 1)) as int] as int);
                Self::lemma_prefix_sum_bounds(card_points@, (k - i) as int);
                Self::lemma_suffix_sum_bounds(card_points@, i as int);
            }

            left_sum = left_sum - card_points[left_card_idx];
            right_sum = right_sum + card_points[right_card_idx];

            proof {
                Self::lemma_prefix_sum_bounds(card_points@, (k - i - 1) as int);
                Self::lemma_suffix_sum_bounds(card_points@, (i + 1) as int);
                assert(left_sum as int + right_sum as int <= k * 10_000) by (nonlinear_arith)
                    requires
                        left_sum as int <= (k - i - 1) * 10_000,
                        right_sum as int <= (i + 1) * 10_000,
                        k <= 100_000,
                        i + 1 <= k;
            }

            let score = left_sum + right_sum;

            proof {
                assert(Self::max_score_spec(card_points@, k as int, (k - i - 1) as int) ==
                    (if Self::prefix_sum(card_points@, (k - i - 1) as int) +
                        Self::suffix_sum(card_points@, (k as int - (k - i - 1) as int)) >=
                        Self::max_score_spec(card_points@, k as int, (k - i) as int)
                    {
                        Self::prefix_sum(card_points@, (k - i - 1) as int) +
                        Self::suffix_sum(card_points@, (k as int - (k - i - 1) as int))
                    } else {
                        Self::max_score_spec(card_points@, k as int, (k - i) as int)
                    }));
            }

            if left_sum + right_sum > best {
                best = left_sum + right_sum;
            }
            i = i + 1;
        }

        best
    }
}

}
