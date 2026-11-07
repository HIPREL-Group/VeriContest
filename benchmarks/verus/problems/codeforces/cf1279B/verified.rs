use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(a: Seq<i64>, i: int) -> int
        decreases i + 1,
    {
        if i < 0 {
            0
        } else {
            a[i] + Self::prefix_sum(a, i - 1)
        }
    }

    pub open spec fn sum_all(a: Seq<i64>, n: int) -> int
        decreases n + 1,
    {
        if n <= 0 {
            0
        } else {
            Self::prefix_sum(a, n - 1)
        }
    }

    pub open spec fn min_overflow_from(a: Seq<i64>, n: int, s: int, i: int) -> int
        decreases n - i,
    {
        if i >= n {
            n
        } else if Self::prefix_sum(a, i) > s {
            i
        } else {
            Self::min_overflow_from(a, n, s, i + 1)
        }
    }

    pub open spec fn min_overflow_index(a: Seq<i64>, n: int, s: int) -> int {
        Self::min_overflow_from(a, n, s, 0)
    }

    pub open spec fn smallest_max_index_on_prefix(a: Seq<i64>, p: int) -> int
        decreases p + 1,
    {
        if p <= 0 {
            0
        } else {
            let prev = Self::smallest_max_index_on_prefix(a, p - 1);
            if a[p] > a[prev] {
                p
            } else {
                prev
            }
        }
    }

    pub open spec fn gifts_from(a: Seq<i64>, n: int, s: int, skip_idx: int, i: int, acc: int, cnt: int) -> int
        decreases n - i,
    {
        if i >= n {
            cnt
        } else if i == skip_idx {
            Self::gifts_from(a, n, s, skip_idx, i + 1, acc, cnt)
        } else {
            let new_acc = acc + a[i];
            if new_acc > s {
                cnt
            } else {
                Self::gifts_from(a, n, s, skip_idx, i + 1, new_acc, cnt + 1)
            }
        }
    }

    pub open spec fn gifts(a: Seq<i64>, n: int, s: int, skip: int) -> int {
        Self::gifts_from(a, n, s, skip - 1, 0, 0, 0)
    }

    proof fn lemma_usize_n_le_100000_implies_int(n: usize)
        requires
            n <= 100000,
        ensures
            n as int <= 100000,
    {
        assert(n <= 100000);
        assert(n as int <= 100000);
    }

    proof fn lemma_prefix_add_next(a: Seq<i64>, i: int)
        requires
            i >= 0,
        ensures
            Self::prefix_sum(a, i - 1) + a[i] == Self::prefix_sum(a, i),
    {
        assert(Self::prefix_sum(a, i) == a[i] + Self::prefix_sum(a, i - 1));
    }

    proof fn lemma_smallest_max_one_step(a: Seq<i64>, t: int, best: int)
        requires
            t >= 1,
            best == Self::smallest_max_index_on_prefix(a, t - 1),
        ensures
            Self::smallest_max_index_on_prefix(a, t) == (if a[t] > a[best] {
                t
            } else {
                best
            }),
    {
        let prev = Self::smallest_max_index_on_prefix(a, t - 1);
        assert(best == prev);
        assert(Self::smallest_max_index_on_prefix(a, t) == if a[t] > a[prev] {
            t
        } else {
            prev
        });
    }

    proof fn lemma_first_gt_s_is_min_overflow(
        a: Seq<i64>,
        n: int,
        s: int,
        j: int,
        k: int,
    )
        requires
            0 <= j && j < n,
            0 <= k && k <= j,
            Self::prefix_sum(a, j) > s,
            forall|t: int| 0 <= t && t < j ==> Self::prefix_sum(a, t) <= s,
        ensures
            Self::min_overflow_from(a, n, s, k) == j,
        decreases j - k,
    {
        if k == j {
            assert(Self::prefix_sum(a, k) > s);
            assert(Self::min_overflow_from(a, n, s, k) == k);
            assert(k == j);
        } else {
            assert(k < j);
            assert(Self::prefix_sum(a, k) <= s);
            assert(Self::min_overflow_from(a, n, s, k) == Self::min_overflow_from(a, n, s, k + 1));
            Self::lemma_first_gt_s_is_min_overflow(a, n, s, j, k + 1);
        }
    }


    proof fn lemma_gifts_from_at_least_cnt(a: Seq<i64>, n: int, s: int, skip_idx: int, i: int, acc: int, cnt: int)
        requires
            0 <= i <= n,
        ensures
            Self::gifts_from(a, n, s, skip_idx, i, acc, cnt) >= cnt,
        decreases n - i,
    {
        if i >= n {
        } else if i == skip_idx {
            Self::lemma_gifts_from_at_least_cnt(a, n, s, skip_idx, i + 1, acc, cnt);
        } else {
            if acc + a[i] > s {
            } else {
                Self::lemma_gifts_from_at_least_cnt(a, n, s, skip_idx, i + 1, acc + a[i], cnt + 1);
            }
        }
    }

    proof fn lemma_gifts_tail_monotonic(a: Seq<i64>, n: int, s: int, skip_idx: int, i: int, acc1: int, acc2: int, cnt: int)
        requires
            0 <= i <= n,
            acc1 <= acc2,
            skip_idx < i,
        ensures
            Self::gifts_from(a, n, s, skip_idx, i, acc1, cnt) >= Self::gifts_from(a, n, s, skip_idx, i, acc2, cnt),
        decreases n - i,
    {
        if i >= n {
        } else {
            if acc2 + a[i] > s {
                if acc1 + a[i] > s {
                } else {
                    Self::lemma_gifts_from_at_least_cnt(a, n, s, skip_idx, i + 1, acc1 + a[i], cnt + 1);
                }
            } else {
                Self::lemma_gifts_tail_monotonic(a, n, s, skip_idx, i + 1, acc1 + a[i], acc2 + a[i], cnt + 1);
            }
        }
    }

    proof fn lemma_gifts_from_noskip_advance(a: Seq<i64>, n: int, s: int, skip_idx: int, i0: int, k: int, d: int, cnt0: int)
        requires
            a.len() == n,
            0 <= i0,
            0 <= k,
            i0 + k <= n,
            skip_idx < i0 || skip_idx >= i0 + k,
            forall|t: int| i0 <= t && t < i0 + k ==> #[trigger] Self::prefix_sum(a, t) <= s + d,
        ensures
            Self::gifts_from(a, n, s, skip_idx, i0, Self::prefix_sum(a, i0 - 1) - d, cnt0)
                == Self::gifts_from(a, n, s, skip_idx, i0 + k, Self::prefix_sum(a, i0 + k - 1) - d, cnt0 + k),
        decreases k,
    {
        if k == 0 {
        } else {
            assert(Self::prefix_sum(a, i0) == a[i0] + Self::prefix_sum(a, i0 - 1));
            Self::lemma_gifts_from_noskip_advance(a, n, s, skip_idx, i0 + 1, k - 1, d, cnt0 + 1);
        }
    }

    proof fn lemma_gifts_from_full_prefix_noskip(a: Seq<i64>, n: int, s: int, skip_idx: int, q: int)
        requires
            a.len() == n,
            0 <= q <= n,
            skip_idx < 0 || skip_idx >= q,
            forall|t: int| 0 <= t && t < q ==> #[trigger] Self::prefix_sum(a, t) <= s,
        ensures
            Self::gifts_from(a, n, s, skip_idx, 0, 0, 0)
                == Self::gifts_from(a, n, s, skip_idx, q, Self::prefix_sum(a, q - 1), q),
    {
        Self::lemma_gifts_from_noskip_advance(a, n, s, skip_idx, 0, q, 0, 0);
    }

    proof fn lemma_gifts_from_full_prefix_skip(a: Seq<i64>, n: int, s: int, skip_idx: int, q: int)
        requires
            a.len() == n,
            0 <= skip_idx < q <= n,
            forall|t: int| 0 <= t && t < skip_idx ==> #[trigger] Self::prefix_sum(a, t) <= s,
            forall|t: int| skip_idx + 1 <= t && t < q ==> #[trigger] Self::prefix_sum(a, t) <= s + a[skip_idx],
        ensures
            Self::gifts_from(a, n, s, skip_idx, 0, 0, 0)
                == Self::gifts_from(a, n, s, skip_idx, q, Self::prefix_sum(a, q - 1) - a[skip_idx], q - 1),
    {
        Self::lemma_gifts_from_noskip_advance(a, n, s, skip_idx, 0, skip_idx, 0, 0);
        assert(Self::gifts_from(a, n, s, skip_idx, skip_idx, Self::prefix_sum(a, skip_idx - 1), skip_idx)
            == Self::gifts_from(a, n, s, skip_idx, skip_idx + 1, Self::prefix_sum(a, skip_idx - 1), skip_idx));
        if q > skip_idx + 1 {
            Self::lemma_gifts_from_noskip_advance(
                a, n, s, skip_idx, skip_idx + 1, q - (skip_idx + 1), a[skip_idx] as int, skip_idx,
            );
            assert(Self::prefix_sum(a, skip_idx) - a[skip_idx] == Self::prefix_sum(a, skip_idx - 1));
        }
    }

    proof fn lemma_gifts_from_irrelevant_skip(a: Seq<i64>, n: int, s: int, skip_idx1: int, skip_idx2: int, i: int, acc: int, cnt: int)
        requires
            0 <= i <= n,
            skip_idx1 < i,
            skip_idx2 < i,
        ensures
            Self::gifts_from(a, n, s, skip_idx1, i, acc, cnt) == Self::gifts_from(a, n, s, skip_idx2, i, acc, cnt),
        decreases n - i,
    {
        if i >= n {
        } else {
            if acc + a[i] > s {
            } else {
                Self::lemma_gifts_from_irrelevant_skip(a, n, s, skip_idx1, skip_idx2, i + 1, acc + a[i], cnt + 1);
            }
        }
    }

    proof fn lemma_min_overflow_prefix_ok(a: Seq<i64>, n: int, s: int, i: int)
        requires
            0 <= i <= n,
        ensures
            i <= Self::min_overflow_from(a, n, s, i) <= n,
            forall|t: int| i <= t && t < Self::min_overflow_from(a, n, s, i) ==> #[trigger] Self::prefix_sum(a, t) <= s,
            Self::min_overflow_from(a, n, s, i) < n ==> Self::prefix_sum(a, Self::min_overflow_from(a, n, s, i)) > s,
        decreases n - i,
    {
        if i >= n {
        } else if Self::prefix_sum(a, i) > s {
        } else {
            Self::lemma_min_overflow_prefix_ok(a, n, s, i + 1);
        }
    }

    proof fn lemma_smallest_max_is_max(a: Seq<i64>, p: int)
        requires
            0 <= p,
        ensures
            0 <= Self::smallest_max_index_on_prefix(a, p) <= p,
            forall|j: int| 0 <= j && j <= p ==> #[trigger] a[j] <= a[Self::smallest_max_index_on_prefix(a, p)],
        decreases p,
    {
        if p <= 0 {
        } else {
            Self::lemma_smallest_max_is_max(a, p - 1);
        }
    }

    proof fn lemma_closed_answer_optimal(a: Seq<i64>, n: int, s: int)
        requires
            a.len() == n,
            0 <= n,
            0 <= s,
            forall|t: int| 0 <= t && t < n ==> a[t] >= 0,
            Self::min_overflow_index(a, n, s) < n,
        ensures
            forall|skip: int| 0 <= skip <= n ==>
                #[trigger] Self::gifts(a, n, s, skip)
                    <= Self::gifts(a, n, s, Self::smallest_max_index_on_prefix(a, Self::min_overflow_index(a, n, s)) + 1),
    {
        let pos = Self::min_overflow_index(a, n, s);
        let best = Self::smallest_max_index_on_prefix(a, pos);
        Self::lemma_min_overflow_prefix_ok(a, n, s, 0);
        Self::lemma_smallest_max_is_max(a, pos);
        assert(0 <= best <= pos < n);

        assert(Self::prefix_sum(a, pos - 1) <= s) by {
            if pos >= 1 {
                assert(0 <= pos - 1 && pos - 1 < pos);
                assert(forall|t: int| 0 <= t && t < pos ==> #[trigger] Self::prefix_sum(a, t) <= s);
            } else {
                assert(Self::prefix_sum(a, pos - 1) == 0);
            }
        };
        assert(Self::prefix_sum(a, pos) - a[best] <= s) by {
            assert(a[best] >= a[pos]);
            assert(Self::prefix_sum(a, pos) == a[pos] + Self::prefix_sum(a, pos - 1));
        };
        Self::lemma_gifts_from_full_prefix_skip(a, n, s, best, pos + 1);
        Self::lemma_gifts_from_at_least_cnt(a, n, s, best, pos + 1, Self::prefix_sum(a, pos) - a[best], pos);

        assert forall|skip: int| 0 <= skip <= n implies
            #[trigger] Self::gifts(a, n, s, skip) <= Self::gifts(a, n, s, best + 1) by {
            let t = skip - 1;
            if t < 0 || t > pos {
                Self::lemma_gifts_from_full_prefix_noskip(a, n, s, t, pos);
                assert(Self::gifts_from(a, n, s, t, pos, Self::prefix_sum(a, pos - 1), pos) == pos) by {
                    assert(Self::prefix_sum(a, pos - 1) + a[pos] > s);
                    assert(Self::prefix_sum(a, pos) == a[pos] + Self::prefix_sum(a, pos - 1));
                };
            } else {
                Self::lemma_smallest_max_is_max(a, pos);
                assert(a[best] >= a[t]);
                if Self::prefix_sum(a, pos) - a[t] > s {
                    Self::lemma_gifts_from_full_prefix_skip(a, n, s, t, pos);
                    assert(Self::gifts_from(a, n, s, t, pos, Self::prefix_sum(a, pos - 1) - a[t], pos - 1) == pos - 1) by {
                        assert(Self::prefix_sum(a, pos - 1) - a[t] + a[pos] > s) by {
                            assert(Self::prefix_sum(a, pos) == a[pos] + Self::prefix_sum(a, pos - 1));
                        };
                    };
                    Self::lemma_gifts_from_at_least_cnt(a, n, s, best, pos + 1, Self::prefix_sum(a, pos) - a[best], pos);
                } else {
                    Self::lemma_gifts_from_full_prefix_skip(a, n, s, t, pos + 1);
                    Self::lemma_gifts_from_irrelevant_skip(
                        a, n, s, best, t, pos + 1, Self::prefix_sum(a, pos) - a[best], pos,
                    );
                    Self::lemma_gifts_tail_monotonic(
                        a, n, s, t, pos + 1, Self::prefix_sum(a, pos) - a[best], Self::prefix_sum(a, pos) - a[t], pos,
                    );
                }
            }
        };
    }

    pub fn verse_for_santa(n: usize, s: i64, a: Vec<i64>) -> (res: i32)
        requires
            1 <= n <= 100000,
            a.len() == n,
            forall|i: int|
                #![trigger a[i]]
                0 <= i && i < n ==> 1 <= a[i] && a[i] <= 1000000000,
            1 <= s <= 1000000000,
        ensures
            Self::sum_all(a@, n as int) <= s as int ==> res == 0,
            Self::sum_all(a@, n as int) > s as int ==> {
                &&& 0 <= res as int <= n as int
                &&& forall|skip: int|
                    0 <= skip <= n as int ==> #[trigger] Self::gifts(a@, n as int, s as int, skip)
                        <= Self::gifts(a@, n as int, s as int, res as int)
            },
    {
        proof {
            Self::lemma_usize_n_le_100000_implies_int(n);
        }
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                a.len() == n,
                1 <= n <= 100000,
                total as int == Self::prefix_sum(a@, (i as int) - 1),
                forall|k: int|
                    #![trigger a@[k]]
                    0 <= k && k < n ==> 1 <= a@[k] && a@[k] <= 1000000000,
                Self::prefix_sum(a@, (i as int) - 1) <= (i as int) * 1000000000,
                (i as int) <= n as int,
            decreases n - i
        {
            proof {
                assert(i < n);
                Self::lemma_prefix_add_next(a@, i as int);
                assert((total as int) + a@[i as int] <= ((i as int) + 1) * 1000000000);
                assert((i as int) + 1 <= n as int);
                assert((total as int) + a@[i as int] <= (n as int) * 1000000000);
                Self::lemma_usize_n_le_100000_implies_int(n);
                assert((n as int) * 1000000000 < 9223372036854775808) by (nonlinear_arith)
                    requires
                        (n as int) <= 100000;
            }
            total = total + a[i];
            proof {
                assert(total as int == Self::prefix_sum(a@, i as int));
                assert(Self::prefix_sum(a@, i as int) <= ((i as int) + 1) * 1000000000);
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(total as int == Self::prefix_sum(a@, (n as int) - 1));
            assert(total as int == Self::sum_all(a@, n as int));
        }
        if total <= s {
            return 0;
        }
        proof {
            assert(total as int == Self::sum_all(a@, n as int));
            assert(Self::sum_all(a@, n as int) > s as int);
        }
        let mut pref: i64 = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                a.len() == n,
                1 <= n <= 100000,
                pref as int == Self::prefix_sum(a@, (j as int) - 1),
                forall|k: int|
                    #![trigger a@[k]]
                    0 <= k && k < n ==> 1 <= a@[k] && a@[k] <= 1000000000,
                forall|t: int|
                    #![trigger Self::prefix_sum(a@, t)]
                    0 <= t && t < j ==> Self::prefix_sum(a@, t) <= s as int,
                Self::prefix_sum(a@, (j as int) - 1) <= (j as int) * 1000000000,
                total as int == Self::sum_all(a@, n as int),
                total as int > s as int,
                1 <= s <= 1000000000,
            decreases n - j
        {
            proof {
                assert(j < n);
                Self::lemma_prefix_add_next(a@, j as int);
                assert((pref as int) + a@[j as int] <= ((j as int) + 1) * 1000000000);
                assert((j as int) + 1 <= n as int);
                assert((pref as int) + a@[j as int] <= (n as int) * 1000000000);
                assert((n as int) <= 100000);
                assert((n as int) * 1000000000 < 9223372036854775808) by (nonlinear_arith)
                    requires
                        (n as int) <= 100000;
            }
            pref = pref + a[j];
            proof {
                assert(pref as int == Self::prefix_sum(a@, j as int));
            }
            if pref > s {
                proof {
                    Self::lemma_first_gt_s_is_min_overflow(a@, n as int, s as int, j as int, 0);
                    assert((j as int) == Self::min_overflow_index(a@, n as int, s as int));
                }
                let mut best_i: usize = 0;
                let mut t: usize = 1;
                while t <= j
                    invariant
                        j < n,
                        a.len() == n,
                        1 <= t,
                        t <= j + 1,
                        best_i <= j,
                        best_i as int == Self::smallest_max_index_on_prefix(a@, (t as int) - 1),
                        pref as int == Self::prefix_sum(a@, j as int),
                        Self::prefix_sum(a@, j as int) > s as int,
                        forall|u: int|
                            #![trigger Self::prefix_sum(a@, u)]
                            0 <= u && u < j ==> Self::prefix_sum(a@, u) <= s as int,
                        1 <= s <= 1000000000,
                    decreases j - t + 1
                {
                    proof {
                        assert(t >= 1);
                        assert(t <= j);
                        assert(j < n);
                        assert(t < n);
                        assert(best_i < n);
                        Self::lemma_smallest_max_one_step(a@, t as int, best_i as int);
                    }
                    if a[t] > a[best_i] {
                        best_i = t;
                    }
                    proof {
                        assert(best_i as int == Self::smallest_max_index_on_prefix(a@, t as int));
                    }
                    t = t + 1;
                }
                proof {
                    assert(t == j + 1);
                    assert(best_i as int == Self::smallest_max_index_on_prefix(a@, j as int));
                    assert forall|k: int| 0 <= k && k < n as int implies #[trigger] a@[k] >= 0 by {
                        assert(1 <= a@[k]);
                    };
                    assert(1 <= s);
                    assert(1 <= s as int);
                    Self::lemma_closed_answer_optimal(a@, n as int, s as int);
                    assert((best_i + 1) as int <= n as int);
                }
                return (best_i + 1) as i32;
            }
            j = j + 1;
        }
        proof {
            assert(j == n);
            assert(Self::prefix_sum(a@, (n as int) - 1) <= s as int);
            assert(Self::prefix_sum(a@, (n as int) - 1) == Self::sum_all(a@, n as int));
            assert(Self::sum_all(a@, n as int) <= s as int);
            assert(total as int > s as int);
            assert(false);
        }
        0
    }
}

}
