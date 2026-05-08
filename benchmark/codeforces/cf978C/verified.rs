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

spec fn int_before_usize(x: int, y: usize) -> bool {
    0 <= x && x < y as int
}

spec fn int_from_usize(x: int, y: usize) -> bool {
    y as int <= x
}

proof fn lemma_prefix_sum_step(piles: Seq<i64>, end: int)
    requires
        0 <= end < piles.len(),
    ensures
        prefix_sum(piles, end + 1) == prefix_sum(piles, end) + piles[end] as int,
{
}

proof fn lemma_prefix_sum_strict_mono(piles: Seq<i64>, start: int, end: int)
    requires
        forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] as int,
        0 <= start && start < end && end <= piles.len(),
    ensures
        prefix_sum(piles, start) < prefix_sum(piles, end),
    decreases end - start,
{
    if start + 1 == end {
        lemma_prefix_sum_step(piles, start);
        assert(1 <= (piles[start] as int));
    } else {
        lemma_prefix_sum_strict_mono(piles, start, end - 1);
        lemma_prefix_sum_step(piles, end - 1);
        assert(prefix_sum(piles, end - 1) < prefix_sum(piles, end));
    }
}

proof fn lemma_prefix_sum_monotone(piles: Seq<i64>, start: int, end: int)
    requires
        forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] as int,
        0 <= start && start <= end && end <= piles.len(),
    ensures
        prefix_sum(piles, start) <= prefix_sum(piles, end),
{
    if start < end {
        lemma_prefix_sum_strict_mono(piles, start, end);
    }
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
        while lo < hi
            invariant
                1 <= prefix.len() && prefix.len() <= 200_000,
                forall|i: int| 0 <= i < prefix.len() ==> 1 <= #[trigger] prefix[i] as int,
                forall|i: int, j: int| 0 <= i < j < prefix.len() ==> prefix[i] < prefix[j],
                1 <= (q as int),
                (q as int) <= prefix[prefix.len() as int - 1] as int,
                0 <= lo && lo <= hi && hi <= prefix.len(),
                forall|j: int| int_before_usize(j, lo) ==> (prefix[j] as int) < (q as int),
                forall|j: int| (int_from_usize(j, hi) && j < prefix.len()) ==> (q as int) <= (prefix[j] as int),
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            proof {
                assert(lo < hi);
                assert(lo <= mid);
                assert(mid < hi);
            }
            if prefix[mid] < q {
                proof {
                    assert forall|j: int| (0 <= j && j < (mid as int) + 1) implies (prefix[j] as int) < (q as int) by {
                        if int_before_usize(j, lo) {
                        } else if j == mid as int {
                        } else {
                            assert((lo as int) <= j && j < mid as int);
                            assert(prefix[j] < prefix[mid as int]);
                        }
                    }
                }
                lo = mid + 1;
            } else {
                proof {
                    assert forall|j: int| ((mid as int) <= j && j < prefix.len()) implies (q as int) <= (prefix[j] as int) by {
                        if j == mid as int {
                        } else {
                            assert((mid as int) < j);
                            assert(prefix[mid as int] < prefix[j]);
                        }
                    }
                }
                hi = mid;
            }
        }
        proof {
            assert(lo == hi);
            assert(lo < prefix.len()) by {
                if lo == prefix.len() {
                    assert(int_before_usize(prefix.len() as int - 1, lo));
                    assert((prefix[prefix.len() as int - 1] as int) < (q as int));
                }
            }
            assert(prefix_interval_contains(prefix@, lo as int, q as int)) by {
                assert(int_from_usize(lo as int, hi));
                assert((q as int) <= (prefix[lo as int] as int));
                if lo == 0 {
                } else {
                    assert(int_before_usize(lo as int - 1, lo));
                    assert((prefix[lo as int - 1] as int) < (q as int));
                }
            }
            assert forall|j: int| (0 <= j && j < prefix.len() && #[trigger] prefix_interval_contains(prefix@, j, q as int)) implies j == lo as int by {
                if int_before_usize(j, lo) {
                    assert(int_before_usize(j, lo));
                    assert((prefix[j] as int) < (q as int));
                } else if int_from_usize(j, lo) && j != lo as int {
                    assert(int_from_usize(j - 1, hi));
                    assert((lo as int) <= j - 1);
                    assert((q as int) <= (prefix[j - 1] as int));
                }
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
        while i < piles.len()
            invariant
                1 <= piles.len() && piles.len() <= 200_000,
                forall|j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] as int && (piles[j] as int) <= 10_000_000_000,
                prefix_sum(piles@, piles.len() as int) <= 9_223_372_036_854_775_807,
                0 <= i && i <= piles.len(),
                prefix.len() == i,
                (sum as int) == prefix_sum(piles@, i as int),
                forall|j: int| 0 <= j < i as int ==> prefix[j] == prefix_sum(piles@, j + 1),
            decreases piles.len() - i,
        {
            proof {
                lemma_prefix_sum_step(piles@, i as int);
                lemma_prefix_sum_monotone(piles@, i as int + 1, piles.len() as int);
                assert((sum as int) + piles[i as int] as int == prefix_sum(piles@, i as int + 1));
                assert((sum as int) + piles[i as int] as int <= 9_223_372_036_854_775_807);
            }
            let ghost old_prefix = prefix@;
            sum += piles[i];
            prefix.push(sum);
            i += 1;
            proof {
                assert(prefix@ == old_prefix.push(sum));
                assert((sum as int) == prefix_sum(piles@, i as int));
                assert forall|j: int| 0 <= j < i as int implies prefix[j] == prefix_sum(piles@, j + 1) by {
                    if j == i as int - 1 {
                        assert(prefix[j] == sum);
                        assert((sum as int) == prefix_sum(piles@, j + 1));
                    } else {
                        assert(j < i as int - 1);
                        assert(prefix[j] == old_prefix[j]);
                    }
                }
            }
        }

        let mut res: Vec<(i64, i64)> = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len()
            invariant
                1 <= piles.len() && piles.len() <= 200_000,
                1 <= queries.len() && queries.len() <= 200_000,
                forall|j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] as int && (piles[j] as int) <= 10_000_000_000,
                prefix_sum(piles@, piles.len() as int) <= 9_223_372_036_854_775_807,
                forall|j: int| 0 <= j < queries.len() ==> 1 <= #[trigger] (queries[j] as int)
                    && (queries[j] as int) <= prefix_sum(piles@, piles.len() as int),
                prefix.len() == piles.len(),
                forall|j: int| 0 <= j < prefix.len() ==> prefix[j] == prefix_sum(piles@, j + 1),
                qi <= queries.len(),
                res.len() == qi,
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
            decreases queries.len() - qi,
        {
            let cur = qi;
            let q = queries[qi];
            proof {
                assert(1 <= (q as int));
                assert((q as int) <= prefix[prefix.len() as int - 1] as int);
                assert forall|j: int| 0 <= j < prefix.len() implies 1 <= #[trigger] prefix[j] as int by {
                    lemma_prefix_sum_strict_mono(piles@, 0, j + 1);
                }
                assert forall|a: int, b: int| 0 <= a < b < prefix.len() implies prefix[a] < prefix[b] by {
                    lemma_prefix_sum_strict_mono(piles@, a + 1, b + 1);
                }
            }
            let idx = Self::locate_dorm(&prefix, queries[qi]) as usize;
            let prev = if idx == 0 { 0i64 } else { prefix[idx - 1] };
            let k = queries[qi] - prev;
            proof {
                let pile = idx + 1;
                assert(0 <= (idx as int));
                assert((idx as int) < prefix.len());
                assert(1 <= (pile as int));
                assert((pile as int) <= piles.len());
                assert(dorm_is_answer(piles@, q as int, pile as int)) by {
                    if idx == 0 {
                        assert(prefix_interval_contains(prefix@, idx as int, q as int));
                        assert(prefix[idx as int] == prefix_sum(piles@, 1));
                    } else {
                        assert(prefix_interval_contains(prefix@, idx as int, q as int));
                        assert(prefix[idx as int] == prefix_sum(piles@, idx as int + 1));
                        assert(prefix[idx as int - 1] == prefix_sum(piles@, idx as int));
                    }
                }
                assert((k as int) == local_room(piles@, q as int, pile as int)) by {
                    if idx == 0 {
                        assert(prev == 0);
                        assert(local_room(piles@, q as int, pile as int) == q as int - prefix_sum(piles@, 0));
                        assert(prefix_sum(piles@, 0) == 0);
                    } else {
                        assert(prev == prefix[idx - 1]);
                        assert(prefix[idx - 1] == prefix_sum(piles@, idx as int));
                        assert(pile as int == idx as int + 1);
                        assert(local_room(piles@, q as int, pile as int) == q as int - prefix_sum(piles@, pile as int - 1));
                        assert(pile as int - 1 == idx as int);
                    }
                }
                assert(1 <= (k as int) && (k as int) <= piles[(pile as int) - 1] as int) by {
                    assert(prefix_interval_contains(prefix@, idx as int, q as int));
                    if idx == 0 {
                        assert(1 <= (q as int));
                        assert((q as int) <= (prefix[0] as int));
                        assert((prefix[0] as int) == (piles[0] as int));
                    } else {
                        assert((prefix[idx as int] as int) - (prefix[idx as int - 1] as int) == (piles[idx as int] as int));
                        assert((q as int) <= (prefix[idx as int] as int));
                        assert((prefix[idx as int - 1] as int) < (q as int));
                    }
                }
                assert forall|j: int|
                    1 <= j <= piles.len() && #[trigger] dorm_is_answer(piles@, q as int, j) implies j == (pile as int) by {
                    assert(prefix_interval_contains(prefix@, j - 1, q as int)) by {
                        if j == 1 {
                            assert(prefix[j - 1] == prefix_sum(piles@, j));
                        } else {
                            assert(prefix[j - 2] == prefix_sum(piles@, j - 1));
                            assert(prefix[j - 1] == prefix_sum(piles@, j));
                        }
                    }
                    assert(j - 1 == idx as int);
                }
            }
            let ghost old_res = res@;
            res.push(((idx + 1) as i64, k));
            qi += 1;
            proof {
                assert(res@ == old_res.push(((idx + 1) as i64, k)));
                assert forall|k2: int|
                    0 <= k2 < res.len() implies 1 <= (res[k2].0 as int)
                        && (res[k2].0 as int) <= piles.len()
                        && 1 <= (res[k2].1 as int)
                        && (res[k2].1 as int) <= piles[(res[k2].0 as int) - 1] as int
                        && dorm_is_answer(piles@, queries[k2] as int, res[k2].0 as int)
                        && (res[k2].1 as int) == local_room(piles@, queries[k2] as int, res[k2].0 as int)
                        && forall|j: int|
                            1 <= j && j <= piles.len() && #[trigger] dorm_is_answer(piles@, queries[k2] as int, j)
                                ==> j == (res[k2].0 as int) by {
                    if k2 == cur as int {
                        assert(res[k2].0 == (idx + 1) as i64);
                        assert(res[k2].1 == k);
                    } else {
                        assert(k2 < cur as int);
                        assert(res[k2].0 == old_res[k2].0);
                        assert(res[k2].1 == old_res[k2].1);
                    }
                }
            }
        }
        proof {
            assert(qi == queries.len());
        }
        res
    }
}

}
