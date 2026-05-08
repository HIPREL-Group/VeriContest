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

    pub open spec fn is_prefix_min_overflow(a: Seq<i64>, n: int, s: int, pos: int) -> bool {
        0 <= pos && pos < n && Self::prefix_sum(a, pos) > s
            && (forall|t: int| 0 <= t && t < pos ==> #[trigger] Self::prefix_sum(a, t) <= s)
    }

    pub open spec fn closed_answer(a: Seq<i64>, n: int, s: int) -> int {
        if Self::sum_all(a, n) <= s {
            0
        } else {
            Self::smallest_max_index_on_prefix(a, Self::min_overflow_index(a, n, s)) + 1
        }
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

    #[verifier::exec_allows_no_decreases_clause]
    pub fn verse_for_santa(n: usize, s: i64, a: Vec<i64>) -> (res: i32)
        requires
            1 <= n <= 100000,
            a.len() == n,
            forall|i: int|
                #![trigger a[i]]
                0 <= i && i < n ==> 1 <= a[i] && a[i] <= 1000000000,
            1 <= s <= 1000000000,
        ensures
            res == Self::closed_answer(a@, n as int, s as int),
            Self::sum_all(a@, n as int) <= s as int ==> res == 0,
            Self::sum_all(a@, n as int) > s as int ==> {
                exists|pos: int|
                    Self::is_prefix_min_overflow(a@, n as int, s as int, pos) && pos
                        == Self::min_overflow_index(a@, n as int, s as int)
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
            proof {
                assert(Self::closed_answer(a@, n as int, s as int) == 0);
            }
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
                    assert(Self::is_prefix_min_overflow(a@, n as int, s as int, j as int));
                    assert((j as int) == Self::min_overflow_index(a@, n as int, s as int));
                    assert(Self::closed_answer(a@, n as int, s as int) == Self::smallest_max_index_on_prefix(
                        a@,
                        Self::min_overflow_index(a@, n as int, s as int),
                    ) + 1);
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
                    assert((best_i + 1) as int == Self::closed_answer(a@, n as int, s as int));
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
