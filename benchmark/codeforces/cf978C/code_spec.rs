use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum_nat(piles: Seq<i64>, end: nat) -> int
    decreases end,
{
    if end == 0 {
        0
    } else {
        prefix_sum_nat(piles, (end - 1) as nat) + piles[end as int - 1] as int
    }
}

pub open spec fn prefix_sum(piles: Seq<i64>, end: int) -> int
    recommends
        0 <= end && end <= piles.len(),
{
    prefix_sum_nat(piles, end as nat)
}

pub open spec fn prefix_interval_contains(prefix: Seq<i64>, idx: int, q: int) -> bool
    recommends
        0 <= idx < prefix.len(),
{
    (if idx == 0 { 0 } else { prefix[idx - 1] as int }) < q && q <= prefix[idx] as int
}

pub open spec fn dorm_is_answer(piles: Seq<i64>, b: int, f: int) -> bool
    recommends
        1 <= f && f <= piles.len(),
{
    prefix_sum(piles, f - 1) < b && b <= prefix_sum(piles, f)
}

pub open spec fn local_room(piles: Seq<i64>, b: int, f: int) -> int
    recommends
        1 <= f && f <= piles.len(),
{
    b - prefix_sum(piles, f - 1)
}

impl Solution {
    fn locate_dorm(prefix: &Vec<i64>, q: i64) -> (res: i32)
        requires
            1 <= prefix.len() && prefix.len() <= 200_000,
            forall|i: int| 0 <= i < prefix.len() ==> 1 <= #[trigger] prefix[i] as int,
            forall|i: int, j: int| 0 <= i < j < prefix.len() ==> prefix[i] < prefix[j],
            1 <= (q as int),
            (q as int) <= prefix[prefix.len() as int - 1] as int,
        ensures
            0 <= (res as int),
            (res as int) < prefix.len(),
            prefix_interval_contains(prefix@, res as int, q as int),
            forall|j: int|
                0 <= j < prefix.len() && #[trigger] prefix_interval_contains(prefix@, j, q as int) ==> j == (res as int),
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

    pub fn deliver_letters(piles: Vec<i64>, queries: Vec<i64>) -> (res: Vec<(i64, i64)>)
        requires
            1 <= piles.len() && piles.len() <= 200_000,
            1 <= queries.len() && queries.len() <= 200_000,
            forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] as int && (piles[i] as int) <= 10_000_000_000,
            prefix_sum(piles@, piles.len() as int) <= 9_223_372_036_854_775_807,
            forall|i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] (queries[i] as int)
                && (queries[i] as int) <= prefix_sum(piles@, piles.len() as int),
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k && k < res.len() ==> 1 <= (res[k].0 as int)
                    && (res[k].0 as int) <= piles.len()
                    && 1 <= (res[k].1 as int)
                    && (res[k].1 as int) <= piles[(res[k].0 as int) - 1] as int
                    && dorm_is_answer(piles@, queries[k] as int, res[k].0 as int)
                    && (res[k].1 as int) == local_room(piles@, queries[k] as int, res[k].0 as int)
                    && forall|j: int|
                        1 <= j && j <= piles.len() && #[trigger] dorm_is_answer(piles@, queries[k] as int, j)
                            ==> j == (res[k].0 as int),
    {
        let mut prefix = Vec::new();
        let mut sum = 0i64;
        let mut i = 0usize;
        while i < piles.len() {
            sum += piles[i];
            prefix.push(sum);
            i += 1;
        }

        let mut res: Vec<(i64, i64)> = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            let idx = Self::locate_dorm(&prefix, queries[qi]) as usize;
            let prev = if idx == 0 { 0i64 } else { prefix[idx - 1] };
            let k = queries[qi] - prev;
            res.push(((idx + 1) as i64, k));
            qi += 1;
        }
        res
    }
}

}
