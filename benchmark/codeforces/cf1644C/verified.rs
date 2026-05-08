use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn neg_inf() -> int {
        -1_000_000_000_000
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn range_sum(a: Seq<i64>, start: int, len: int) -> int
        decreases if len <= 0 { 0 } else { len },
    {
        if start < 0 || len <= 0 || start + len > a.len() {
            0
        } else {
            a[start] as int + Self::range_sum(a, start + 1, len - 1)
        }
    }

    pub open spec fn max_len_sum_upto(a: Seq<i64>, len: int, upto: int) -> int
        decreases if upto <= 0 { 0 } else { upto },
    {
        if len <= 0 {
            0
        } else if upto <= 0 {
            Self::neg_inf()
        } else {
            let prev = Self::max_len_sum_upto(a, len, upto - 1);
            let cur = Self::range_sum(a, upto - 1, len);
            if prev <= cur { cur } else { prev }
        }
    }

    pub open spec fn max_len_sum(a: Seq<i64>, len: int) -> int {
        if len == 0 {
            0
        } else if len < 0 || len > a.len() {
            Self::neg_inf()
        } else {
            Self::max_len_sum_upto(a, len, a.len() as int - len + 1)
        }
    }

    pub open spec fn candidate_value(a: Seq<i64>, x: int, k: int, len: int) -> int {
        Self::max_len_sum(a, len) + x * Self::min_int(k, len)
    }

    pub open spec fn best_value_upto(a: Seq<i64>, x: int, k: int, upto: int) -> int
        decreases if upto <= 0 { 0 } else { upto },
    {
        if upto <= 0 {
            Self::neg_inf()
        } else {
            let prev = Self::best_value_upto(a, x, k, upto - 1);
            let cur = Self::candidate_value(a, x, k, upto - 1);
            if prev <= cur { cur } else { prev }
        }
    }

    pub open spec fn best_value_for_k(a: Seq<i64>, x: int, k: int) -> int {
        Self::best_value_upto(a, x, k, a.len() as int + 1)
    }

    pub open spec fn candidate_from_best(best: Seq<i64>, x: int, k: int, len: int) -> int {
        if len < 0 || len >= best.len() {
            Self::neg_inf()
        } else {
            best[len] as int + x * Self::min_int(k, len)
        }
    }

    pub open spec fn best_from_best_upto(best: Seq<i64>, x: int, k: int, upto: int) -> int
        decreases if upto <= 0 { 0 } else { upto },
    {
        if upto <= 0 {
            Self::neg_inf()
        } else {
            let prev = Self::best_from_best_upto(best, x, k, upto - 1);
            let cur = Self::candidate_from_best(best, x, k, upto - 1);
            if prev <= cur { cur } else { prev }
        }
    }

    pub open spec fn best_from_best(best: Seq<i64>, x: int, k: int) -> int {
        Self::best_from_best_upto(best, x, k, best.len() as int)
    }

    proof fn lemma_range_sum_bounds(a: Seq<i64>, start: int, len: int)
        requires
            forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a[i] <= 100000,
            0 <= start,
            0 <= len,
            start + len <= a.len(),
        ensures
            -100000 * len <= Self::range_sum(a, start, len) <= 100000 * len,
        decreases len,
    {
        if len > 0 {
            Self::lemma_range_sum_bounds(a, start + 1, len - 1);
        }
    }

    proof fn lemma_range_sum_extend(a: Seq<i64>, start: int, len: int)
        requires
            0 <= start,
            0 <= len,
            start + len < a.len(),
        ensures
            Self::range_sum(a, start, len + 1) == Self::range_sum(a, start, len) + a[start + len] as int,
        decreases len,
    {
        if len == 0 {
            assert(start + 1 <= a.len());
            assert(Self::range_sum(a, start, 1) == a[start] as int + Self::range_sum(a, start + 1, 0));
            assert(Self::range_sum(a, start, 0) == 0);
        } else {
            Self::lemma_range_sum_extend(a, start + 1, len - 1);
            assert(Self::range_sum(a, start, len + 1) == a[start] as int + Self::range_sum(a, start + 1, len));
            assert(Self::range_sum(a, start, len) == a[start] as int + Self::range_sum(a, start + 1, len - 1));
        }
    }

    proof fn lemma_range_sum_slide(a: Seq<i64>, start: int, len: int)
        requires
            0 <= start,
            1 <= len,
            start + len < a.len(),
        ensures
            Self::range_sum(a, start + 1, len)
                == Self::range_sum(a, start, len) - a[start] as int + a[start + len] as int,
        decreases len,
    {
        if len == 1 {
            assert(start + 2 <= a.len());
            assert(Self::range_sum(a, start + 1, 1) == a[start + 1] as int + Self::range_sum(a, start + 2, 0));
            assert(Self::range_sum(a, start, 1) == a[start] as int + Self::range_sum(a, start + 1, 0));
        } else {
            Self::lemma_range_sum_slide(a, start + 1, len - 1);
            assert(Self::range_sum(a, start + 1, len) == a[start + 1] as int + Self::range_sum(a, start + 2, len - 1));
            assert(Self::range_sum(a, start, len) == a[start] as int + Self::range_sum(a, start + 1, len - 1));
        }
    }

    proof fn lemma_best_from_best_matches_array(a: Seq<i64>, best: Seq<i64>, x: int, k: int, upto: int)
        requires
            best.len() == a.len() + 1,
            forall|l: int| 0 <= l < best.len() ==> #[trigger] best[l] as int == Self::max_len_sum(a, l),
            0 <= upto <= best.len(),
        ensures
            Self::best_from_best_upto(best, x, k, upto) == Self::best_value_upto(a, x, k, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_best_from_best_matches_array(a, best, x, k, upto - 1);
            assert(Self::candidate_from_best(best, x, k, upto - 1) == Self::candidate_value(a, x, k, upto - 1));
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn max_sum_for_len(a: &Vec<i64>, len: usize) -> (res: i64)
        requires
            1 <= a.len() <= 5000,
            1 <= len <= a.len(),
            forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
        ensures
            res as int == Self::max_len_sum(a@, len as int),
            -500000000 <= res as int <= 500000000,
    {
        let n = a.len();
        let mut j: usize = 0;
        let mut window_sum: i64 = 0;
        while j < len
            invariant
                0 <= j <= len <= n <= 5000,
                n == a.len(),
                forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
                window_sum as int == Self::range_sum(a@, 0, j as int),
                -100000 * j as int <= window_sum as int <= 100000 * j as int,
            decreases len - j,
        {
            let j0 = j;
            proof {
                assert(0 <= j0 < n);
                Self::lemma_range_sum_extend(a@, 0, j0 as int);
                assert(-100000 <= a@[j0 as int] <= 100000);
                assert(-100000 * (j0 as int + 1) <= window_sum as int + a@[j0 as int] as int <= 100000 * (j0 as int + 1)) by(nonlinear_arith)
                    requires
                        -100000 * j0 as int <= window_sum as int <= 100000 * j0 as int,
                        -100000 <= a@[j0 as int] <= 100000;
            }
            window_sum = window_sum + a[j0];
            j = j0 + 1;
            proof {
                Self::lemma_range_sum_bounds(a@, 0, j as int);
            }
        }
        let mut best_len = window_sum;
        let mut start: usize = 0;
        proof {
            assert(Self::max_len_sum_upto(a@, len as int, 0) == Self::neg_inf());
            assert(Self::max_len_sum_upto(a@, len as int, 1)
                == if Self::max_len_sum_upto(a@, len as int, 0) <= Self::range_sum(a@, 0, len as int) {
                    Self::range_sum(a@, 0, len as int)
                } else {
                    Self::max_len_sum_upto(a@, len as int, 0)
                });
            assert(best_len as int == Self::max_len_sum_upto(a@, len as int, 1));
        }
        while start + len < n
            invariant
                1 <= len <= n <= 5000,
                n == a.len(),
                0 <= start <= n - len,
                forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
                window_sum as int == Self::range_sum(a@, start as int, len as int),
                best_len as int == Self::max_len_sum_upto(a@, len as int, start as int + 1),
                -100000 * len as int <= window_sum as int <= 100000 * len as int,
                -100000 * len as int <= best_len as int <= 100000 * len as int,
            decreases n - len - start,
        {
            let start0 = start;
            proof {
                assert(0 <= start0 < n);
                assert(start0 + len < n);
                Self::lemma_range_sum_slide(a@, start0 as int, len as int);
                assert(-100000 <= a@[start0 as int] <= 100000);
                assert(-100000 <= a@[(start0 + len) as int] <= 100000);
                assert(-600000000 <= window_sum as int - a@[start0 as int] as int <= 600000000) by(nonlinear_arith)
                    requires
                        -100000 * len as int <= window_sum as int <= 100000 * len as int,
                        len <= 5000,
                        -100000 <= a@[start0 as int] <= 100000;
                assert(-700000000 <= window_sum as int - a@[start0 as int] as int + a@[(start0 + len) as int] as int <= 700000000) by(nonlinear_arith)
                    requires
                        -600000000 <= window_sum as int - a@[start0 as int] as int <= 600000000,
                        -100000 <= a@[(start0 + len) as int] <= 100000;
            }
            window_sum = window_sum - a[start0] + a[start0 + len];
            start = start0 + 1;
            if window_sum > best_len {
                best_len = window_sum;
            }
            proof {
                Self::lemma_range_sum_bounds(a@, start as int, len as int);
                assert(Self::max_len_sum_upto(a@, len as int, start as int + 1)
                    == if Self::max_len_sum_upto(a@, len as int, start as int) <= Self::range_sum(a@, start as int, len as int) {
                        Self::range_sum(a@, start as int, len as int)
                    } else {
                        Self::max_len_sum_upto(a@, len as int, start as int)
                    });
            }
        }
        proof {
            assert(start == n - len);
            assert(start as int + 1 == a@.len() as int - len as int + 1);
            assert(best_len as int == Self::max_len_sum(a@, len as int));
        }
        best_len
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn best_answer_from_best(best: &Vec<i64>, x: i64, k: usize) -> (res: i64)
        requires
            1 <= best.len() <= 5001,
            0 <= x <= 100000,
            0 <= k < best.len(),
            forall|l: int| 0 <= l < best.len() ==> -500000000 <= #[trigger] best@[l] as int <= 500000000,
        ensures
            res as int == Self::best_from_best(best@, x as int, k as int),
            Self::neg_inf() <= res as int <= 1000000000,
    {
        let n = best.len() - 1;
        let mut cur: i64 = -1_000_000_000_000;
        let mut used_len: usize = 0;
        while used_len <= n
            invariant
                0 <= used_len <= n + 1,
                1 <= best.len() == n + 1,
                n <= 5000,
                0 <= x <= 100000,
                0 <= k < best.len(),
                forall|l: int| 0 <= l < best.len() ==> -500000000 <= #[trigger] best@[l] as int <= 500000000,
                cur as int == Self::best_from_best_upto(best@, x as int, k as int, used_len as int),
                Self::neg_inf() <= cur as int <= 1000000000,
            decreases n + 1 - used_len,
        {
            let used0 = used_len;
            let boosted = if used0 < k { used0 as i64 } else { k as i64 };
            proof {
                if used0 < k {
                    assert(boosted == used0 as i64);
                    assert(Self::min_int(k as int, used0 as int) == used0 as int);
                    assert(0 <= boosted);
                    assert(boosted <= 5000) by(nonlinear_arith)
                        requires
                            boosted == used0 as i64,
                            used0 <= n,
                            n <= 5000;
                } else {
                    assert(boosted == k as i64);
                    assert(Self::min_int(k as int, used0 as int) == k as int);
                    assert(0 <= boosted);
                    assert(boosted <= 5000) by(nonlinear_arith)
                        requires
                            boosted == k as i64,
                            k < n + 1,
                            n <= 5000;
                }
                assert(boosted as int == Self::min_int(k as int, used0 as int));
                assert(0 <= x as int * boosted as int <= 500000000) by(nonlinear_arith)
                    requires
                        0 <= x <= 100000,
                        0 <= boosted <= 5000;
                assert(-500000000 <= best@[used0 as int] as int <= 500000000);
                assert(Self::neg_inf() <= best@[used0 as int] as int + x as int * boosted as int <= 1000000000);
            }
            let cand = best[used0] + x * boosted;
            if cand > cur {
                cur = cand;
            }
            used_len = used0 + 1;
            proof {
                assert(Self::best_from_best_upto(best@, x as int, k as int, used_len as int)
                    == if Self::best_from_best_upto(best@, x as int, k as int, used0 as int)
                        <= Self::candidate_from_best(best@, x as int, k as int, used0 as int) {
                        Self::candidate_from_best(best@, x as int, k as int, used0 as int)
                    } else {
                        Self::best_from_best_upto(best@, x as int, k as int, used0 as int)
                    });
            }
        }
        cur
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn increase_subarray_sums(a: Vec<i64>, x: i64) -> (res: Vec<i64>)
        requires
            1 <= a.len() <= 5000,
            0 <= x <= 100000,
            forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
        ensures
            res.len() == a.len() + 1,
            forall|k: int| 0 <= k < res.len() ==> #[trigger] res@[k] as int == Self::best_value_for_k(a@, x as int, k),
    {
        let n = a.len();
        let mut best: Vec<i64> = Vec::new();
        best.push(0);
        let mut len: usize = 1;
        while len <= n
            invariant
                best.len() == len,
                n == a.len(),
                1 <= len <= n + 1,
                n <= 5000,
                forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
                forall|l: int| 0 <= l < best.len() ==> #[trigger] best@[l] as int == Self::max_len_sum(a@, l),
                forall|l: int| 0 <= l < best.len() ==> -500000000 <= #[trigger] best@[l] as int <= 500000000,
            decreases n + 1 - len,
        {
            let best_len = Solution::max_sum_for_len(&a, len);
            best.push(best_len);
            len = len + 1;
        }

        let mut ans: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= n
            invariant
                ans.len() == k,
                0 <= k <= n + 1,
                best.len() == n + 1,
                n == a.len(),
                n <= 5000,
                forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
                forall|l: int| 0 <= l < best.len() ==> #[trigger] best@[l] as int == Self::max_len_sum(a@, l),
                forall|l: int| 0 <= l < best.len() ==> -500000000 <= #[trigger] best@[l] as int <= 500000000,
                forall|q: int| 0 <= q < ans.len() ==> #[trigger] ans@[q] as int == Self::best_value_for_k(a@, x as int, q),
                0 <= x <= 100000,
            decreases n + 1 - k,
        {
            let cur = Solution::best_answer_from_best(&best, x, k);
            proof {
                Self::lemma_best_from_best_matches_array(a@, best@, x as int, k as int, best.len() as int);
                assert(cur as int == Self::best_value_for_k(a@, x as int, k as int));
            }
            ans.push(cur);
            k = k + 1;
        }
        proof {
            assert(k > n);
            assert(k == n + 1);
            assert(ans.len() == n + 1);
        }
        ans
    }
}

}
