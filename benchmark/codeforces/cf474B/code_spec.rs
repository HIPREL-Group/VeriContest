use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum_nat(piles: Seq<i32>, end: nat) -> int
    decreases end,
{
    if end == 0 {
        0
    } else {
        prefix_sum_nat(piles, (end - 1) as nat) + piles[end as int - 1] as int
    }
}

pub open spec fn prefix_sum(piles: Seq<i32>, end: int) -> int
    recommends
        0 <= end && end <= piles.len(),
{
    prefix_sum_nat(piles, end as nat)
}

pub open spec fn prefix_interval_contains(prefix: Seq<i32>, idx: int, q: int) -> bool
    recommends
        0 <= idx < prefix.len(),
{
    (if idx == 0 { 0 } else { prefix[idx - 1] as int }) < q && q <= prefix[idx] as int
}

pub open spec fn pile_index_is_answer(piles: Seq<i32>, q: int, pile: int) -> bool
    recommends
        1 <= pile && pile <= piles.len(),
{
    prefix_sum(piles, pile - 1) < q && q <= prefix_sum(piles, pile)
}

impl Solution {
    fn locate_pile(prefix: &Vec<i32>, q: i32) -> (res: i32)
        requires
            1 <= prefix.len() && prefix.len() <= 100_000,
            forall|i: int| 0 <= i < prefix.len() ==> 1 <= #[trigger] prefix[i],
            forall|i: int, j: int| 0 <= i < j < prefix.len() ==> prefix[i] < prefix[j],
            1 <= (q as int),
            (q as int) <= prefix[prefix.len() as int - 1] as int,
        ensures
            0 <= (res as int),
            (res as int) < prefix.len(),
            prefix_interval_contains(prefix@, res as int, q as int),
            forall|j: int| 0 <= j < prefix.len() && #[trigger] prefix_interval_contains(prefix@, j, q as int) ==> j == (res as int),
    {
        let mut lo = 0usize;
        let mut hi = prefix.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if prefix[mid] < q {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo as i32
    }

    pub fn find_worm_piles(piles: Vec<i32>, queries: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= piles.len() && piles.len() <= 100_000,
            1 <= queries.len() && queries.len() <= 100_000,
            forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] && piles[i] <= 1000,
            prefix_sum(piles@, piles.len() as int) <= 1_000_000,
            forall|i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] (queries[i] as int) && (queries[i] as int) <= prefix_sum(piles@, piles.len() as int),
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k && k < res.len() ==> 1 <= (res[k] as int)
                    && (res[k] as int) <= piles.len()
                    && pile_index_is_answer(piles@, queries[k] as int, res[k] as int)
                    && forall|j: int|
                        1 <= j && j <= piles.len() && #[trigger] pile_index_is_answer(piles@, queries[k] as int, j) ==> j == (res[k] as int),
    {
        let mut prefix = Vec::new();
        let mut sum = 0i32;
        let mut i = 0usize;
        while i < piles.len() {
            sum += piles[i];
            prefix.push(sum);
            i += 1;
        }

        let mut res = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            res.push(Self::locate_pile(&prefix, queries[qi]) + 1);
            qi += 1;
        }
        res
    }
}

}
