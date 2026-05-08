use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn walk_feasible(a: Seq<i32>, b: Seq<i32>, k: int) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] >= a[i]
    &&& forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] b[i] + b[i + 1] >= k
}

pub open spec fn greedy_walk_at(a: Seq<i32>, k: int, inat: nat) -> int
    recommends
        (inat as int) < a.len(),
    decreases
        inat,
{
    let i = inat as int;
    if inat == 0nat {
        if (a[0] as int) >= k - k {
            a[0] as int
        } else {
            k - k
        }
    } else {
        let prev = greedy_walk_at(a, k, (inat - 1) as nat);
        if (a[i] as int) >= k - prev {
            a[i] as int
        } else {
            k - prev
        }
    }
}

pub open spec fn greedy_additional_prefix(a: Seq<i32>, k: int, end: nat) -> int
    recommends
        (end as int) <= a.len(),
    decreases
        end,
{
    if end == 0nat {
        0
    } else {
        let last = (end - 1) as int;
        greedy_additional_prefix(a, k, (end - 1) as nat) + (greedy_walk_at(a, k, (end - 1) as nat) - a[last] as int)
    }
}

proof fn lemma_greedy_additional_prefix_bound(a: Seq<i32>, k: int, end: nat)
    requires
        (end as int) <= a.len(),
        forall|t: int| 0 <= t < a.len() ==> 0 <= #[trigger] (a[t] as int) && (a[t] as int) <= 500,
        1 <= k && k <= 500,
    ensures
        greedy_additional_prefix(a, k, end) <= 500 * (end as int),
    decreases
        end,
{
    if end == 0nat {
    } else {
        lemma_greedy_additional_prefix_bound(a, k, (end - 1) as nat);
        let last = (end - 1) as int;
        lemma_greedy_walk_at_le_500(a, k, (end - 1) as nat);
        assert(greedy_walk_at(a, k, (end - 1) as nat) - a[last] as int <= 500);
        assert(
            greedy_additional_prefix(a, k, end)
                == greedy_additional_prefix(a, k, (end - 1) as nat)
                    + (greedy_walk_at(a, k, (end - 1) as nat) - a[last] as int)
        );
        assert(
            greedy_additional_prefix(a, k, end) <= 500 * ((end - 1) as int) + 500
        );
        assert(500 * ((end - 1) as int) + 500 == 500 * (end as int));
    }
}

proof fn lemma_greedy_additional_prefix_step(a: Seq<i32>, k: int, end: int)
    requires
        0 <= end < a.len(),
    ensures
        greedy_additional_prefix(a, k, (end + 1) as nat)
            == greedy_additional_prefix(a, k, end as nat)
                + (greedy_walk_at(a, k, end as nat) - a[end] as int),
{
    let e1 = (end + 1) as nat;
    assert(e1 > 0nat);
    assert(
        greedy_additional_prefix(a, k, e1) == greedy_additional_prefix(a, k, end as nat)
            + (greedy_walk_at(a, k, end as nat) - a[end] as int)
    );
}

proof fn lemma_greedy_walk_at_ge_a(a: Seq<i32>, k: int, inat: nat)
    requires
        (inat as int) < a.len(),
        forall|t: int| 0 <= t < a.len() ==> 0 <= #[trigger] a[t] as int,
    ensures
        greedy_walk_at(a, k, inat) >= a[inat as int] as int,
    decreases
        inat,
{
    let i = inat as int;
    if inat == 0nat {
        assert((a[0] as int) >= 0);
        assert(k - k == 0);
        assert((a[0] as int) >= k - k);
        assert(greedy_walk_at(a, k, 0nat) == a[0] as int);
    } else {
        lemma_greedy_walk_at_ge_a(a, k, (inat - 1) as nat);
        let prev_g = greedy_walk_at(a, k, (inat - 1) as nat);
        if (a[i] as int) >= k - prev_g {
            assert(greedy_walk_at(a, k, inat) == a[i] as int);
        } else {
            assert(greedy_walk_at(a, k, inat) == k - prev_g);
            assert((a[i] as int) < k - prev_g);
        }
    }
}

proof fn lemma_greedy_adjacent_sum(a: Seq<i32>, k: int, i: int)
    requires
        0 <= i < a.len() - 1,
        forall|t: int| 0 <= t < a.len() ==> 0 <= #[trigger] a[t] as int,
    ensures
        greedy_walk_at(a, k, i as nat) + greedy_walk_at(a, k, (i + 1) as nat) >= k,
{
    let gi = greedy_walk_at(a, k, i as nat);
    let gip1 = greedy_walk_at(a, k, (i + 1) as nat);
    assert(
        greedy_walk_at(a, k, (i + 1) as nat) == if (a[i + 1] as int) >= k - gi {
            a[i + 1] as int
        } else {
            k - gi
        }
    );
    if (a[i + 1] as int) >= k - gi {
        assert(gip1 == a[i + 1] as int);
        assert(gi + gip1 >= gi + (k - gi));
        assert(gi + (k - gi) == k);
        assert(gi + gip1 >= k);
    } else {
        assert(gip1 == k - gi);
        assert(gi + gip1 == k);
    }
}

proof fn lemma_bi_matches_greedy(a: Seq<i32>, k: int, idx: int, prev: i32)
    requires
        0 <= idx < a.len(),
        (prev as int) == if idx == 0 {
            k
        } else {
            greedy_walk_at(a, k, ((idx - 1) as nat))
        },
        forall|t: int| 0 <= t < a.len() ==> 0 <= #[trigger] a[t] as int,
    ensures
        (if (a[idx] as int) >= k - (prev as int) {
            a[idx] as int
        } else {
            k - (prev as int)
        }) == greedy_walk_at(a, k, idx as nat),
{
    if idx == 0 {
        assert((prev as int) == k);
        assert(k - (prev as int) == k - k);
        assert(greedy_walk_at(a, k, 0nat) == if (a[0] as int) >= k - k {
            a[0] as int
        } else {
            k - k
        });
    } else {
        let gprev = greedy_walk_at(a, k, ((idx - 1) as nat));
        assert((prev as int) == gprev);
        assert(
            greedy_walk_at(a, k, idx as nat) == if (a[idx] as int) >= k - gprev {
                a[idx] as int
            } else {
                k - gprev
            }
        );
    }
}

proof fn lemma_greedy_walk_at_le_500(a: Seq<i32>, k: int, inat: nat)
    requires
        (inat as int) < a.len(),
        forall|t: int| 0 <= t < a.len() ==> 0 <= #[trigger] (a[t] as int) && (a[t] as int) <= 500,
        1 <= k && k <= 500,
    ensures
        greedy_walk_at(a, k, inat) <= 500,
    decreases
        inat,
{
    if inat == 0nat {
        assert(greedy_walk_at(a, k, 0nat) == a[0] as int || greedy_walk_at(a, k, 0nat) == 0);
        assert((a[0] as int) <= 500);
        assert(greedy_walk_at(a, k, 0nat) <= 500);
    } else {
        lemma_greedy_walk_at_le_500(a, k, (inat - 1) as nat);
        let prev = greedy_walk_at(a, k, (inat - 1) as nat);
        assert(prev <= 500);
        let i = inat as int;
        assert(k - prev >= -500);
        assert(greedy_walk_at(a, k, inat) == if (a[i] as int) >= k - prev {
            a[i] as int
        } else {
            k - prev
        });
        if (a[i] as int) >= k - prev {
            assert((a[i] as int) <= 500);
            assert(greedy_walk_at(a, k, inat) <= 500);
        } else {
            assert(greedy_walk_at(a, k, inat) == k - prev);
            assert(k <= 500);
            assert(prev >= 0);
            assert(k - prev <= 500);
        }
    }
}

proof fn lemma_walk_feasible_from_greedy(a: Seq<i32>, b: Seq<i32>, k: int)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] == greedy_walk_at(a, k, i as nat),
        forall|t: int| 0 <= t < a.len() ==> 0 <= #[trigger] a[t] as int,
    ensures
        walk_feasible(a, b, k),
{
    assert forall|i: int| 0 <= i < a.len() implies b[i] >= a[i] by {
        lemma_greedy_walk_at_ge_a(a, k, i as nat);
    }
    assert forall|i: int| 0 <= i < a.len() - 1 implies #[trigger] b[i] + b[i + 1] >= k by {
        lemma_greedy_adjacent_sum(a, k, i);
    }
}

impl Solution {
    pub fn cormen_walk_schedule(a: Vec<i32>, k: i32) -> (result: (i64, Vec<i32>))
        requires
            1 <= a.len() && a.len() <= 500,
            1 <= k <= 500,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] && a[i] <= 500,
        ensures
            walk_feasible(a@, result.1@, k as int),
            result.0 as int == greedy_additional_prefix(a@, k as int, a.len() as nat),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] result.1[i] == greedy_walk_at(a@, k as int, i as nat),
    {
        let n = a.len();
        let ghost a_seq = a@;
        let mut b: Vec<i32> = Vec::new();
        let mut total: i64 = 0;
        let mut prev: i32 = k;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n <= 500,
                i <= n,
                b.len() == i,
                a@ == a_seq,
                1 <= k && k <= 500,
                0 <= prev && prev <= 500,
                total as int == greedy_additional_prefix(a_seq, k as int, b.len() as nat),
                (prev as int) == if i == 0 {
                    k as int
                } else {
                    greedy_walk_at(a_seq, k as int, ((i - 1) as nat))
                },
                forall|j: int| 0 <= j < i as int ==> #[trigger] b[j] == greedy_walk_at(a_seq, k as int, j as nat),
                forall|t: int|
                    0 <= t < a_seq.len() ==> 0 <= #[trigger] a_seq[t] as int && (a_seq[t] as int) <= 500,
                (total as int) <= 500 * (b.len() as int),
            decreases
                n - i,
        {
            let ai = a[i];
            let kd = k as i64;
            let pred = prev as i64;
            proof {
                lemma_bi_matches_greedy(a_seq, k as int, i as int, prev);
                assert(kd - pred == (k as i64) - (prev as i64));
                assert(
                    ((ai as i64) >= kd - pred) == ((ai as int) >= (k as int) - (prev as int))
                );
                assert(
                    (if (ai as i64) >= kd - pred { ai as int } else { (kd - pred) as int })
                        == (if (ai as int) >= k - (prev as int) { ai as int } else { k - (prev as int) })
                );
                assert(
                    (if (ai as int) >= k - (prev as int) { ai as int } else { k - (prev as int) })
                        == greedy_walk_at(a_seq, k as int, i as nat)
                );
            }
            let bi = if (ai as i64) >= kd - pred { ai } else { (kd - pred) as i32 };
            proof {
                assert(bi as int == greedy_walk_at(a_seq, k as int, i as nat));
                lemma_greedy_additional_prefix_step(a_seq, k as int, i as int);
                assert(
                    (total as int) + (bi as int - ai as int)
                        == greedy_additional_prefix(a_seq, k as int, (i as int + 1) as nat)
                );
            }
            total = total + (bi as i64 - ai as i64);
            b.push(bi);
            proof {
                lemma_greedy_walk_at_le_500(a_seq, k as int, i as nat);
                assert(bi <= 500);
                assert((total as int) == greedy_additional_prefix(a_seq, k as int, b.len() as nat));
                lemma_greedy_additional_prefix_bound(a_seq, k as int, b.len() as nat);
                assert((total as int) <= 500 * (b.len() as int));
                assert((total as int) <= 500 * (n as int));
                assert(total <= (500 * n) as i64);
            }
            prev = bi;
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(b.len() == n);
            assert(forall|j: int| 0 <= j < a_seq.len() as int ==> b[j] == greedy_walk_at(a_seq, k as int, j as nat));
            assert(total as int == greedy_additional_prefix(a_seq, k as int, a_seq.len() as nat));
            lemma_walk_feasible_from_greedy(a_seq, b@, k as int);
        }
        (total, b)
    }
}

}
