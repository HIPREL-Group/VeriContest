use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn freq_at(requests: Seq<Vec<i32>>, idx: int, k: int) -> int
        decreases requests.len() - k
    {
        if k >= requests.len() as int {
            0
        } else {
            (if requests[k]@[0] as int <= idx && idx <= requests[k]@[1] as int {
                1int
            } else {
                0int
            }) + Self::freq_at(requests, idx, k + 1)
        }
    }

    pub open spec fn freq_vec(requests: Seq<Vec<i32>>, n: int) -> Seq<int> {
        Seq::new(n as nat, |i: int| Self::freq_at(requests, i, 0))
    }

    pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn dot_product_int(a: Seq<int>, b: Seq<int>, k: int) -> int
        decreases a.len() - k
    {
        if k >= a.len() as int {
            0
        } else {
            a[k] * b[k] + Self::dot_product_int(a, b, k + 1)
        }
    }

    pub open spec fn is_sorted_int(s: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_int(s: Seq<int>, v: int) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() == v { 1int } else { 0int })
                + Self::count_int(s.drop_last(), v)
        }
    }

    pub open spec fn is_perm_int(a: Seq<int>, b: Seq<int>) -> bool {
        a.len() == b.len()
            && forall |v: int| Self::count_int(a, v) == Self::count_int(b, v)
    }

    pub open spec fn to_int_seq_i64(s: Seq<i64>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len()
            && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ_i64(s: Seq<i64>, val: i64) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ_i64(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm_i64(a: Seq<i64>, b: Seq<i64>) -> bool {
        a.len() == b.len()
            && forall |v: i64| Self::count_occ_i64(a, v) == Self::count_occ_i64(b, v)
    }

    pub open spec fn is_sorted_i64(s: Seq<i64>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_in_range_int(s: Seq<int>, v: int, start: int, end: int) -> int
        decreases end - start when start <= end
    {
        if start >= end { 0 }
        else {
            (if s[start] == v { 1int } else { 0int })
                + Self::count_in_range_int(s, v, start + 1, end)
        }
    }

    

    proof fn freq_at_bounded(requests: Seq<Vec<i32>>, idx: int, k: int)
        requires
            0 <= k,
            forall |i: int| 0 <= i < requests.len() ==> (
                (#[trigger] requests[i])@.len() == 2
                    && 0 <= requests[i]@[0]
                    && requests[i]@[0] <= requests[i]@[1]
            ),
        ensures
            0 <= Self::freq_at(requests, idx, k),
            k <= requests.len() as int ==> Self::freq_at(requests, idx, k) <= requests.len() as int - k,
        decreases requests.len() - k
    {
        if k < requests.len() as int {
            Self::freq_at_bounded(requests, idx, k + 1);
        }
    }

    proof fn count_int_nonneg(s: Seq<int>, v: int)
        ensures Self::count_int(s, v) >= 0
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_int_nonneg(s.drop_last(), v);
        }
    }

    proof fn count_int_positive_exists(s: Seq<int>, v: int)
        requires Self::count_int(s, v) >= 1
        ensures exists |k: int| 0 <= k < s.len() && s[k] == v
        decreases s.len()
    {
        if s.len() == 0 {
        } else {
            Self::count_int_nonneg(s.drop_last(), v);
            if s.last() == v {
                assert(s[s.len() as int - 1] == v);
            } else {
                Self::count_int_positive_exists(s.drop_last(), v);
                let k = choose |k: int| 0 <= k < s.drop_last().len() && s.drop_last()[k] == v;
                assert(s[k] == v);
            }
        }
    }

    proof fn count_in_range_additive_int(s: Seq<int>, v: int, a: int, b: int, c: int)
        requires a <= b, b <= c
        ensures Self::count_in_range_int(s, v, a, c)
            == Self::count_in_range_int(s, v, a, b) + Self::count_in_range_int(s, v, b, c)
        decreases b - a
    {
        if a < b {
            Self::count_in_range_additive_int(s, v, a + 1, b, c);
        }
    }

    proof fn count_in_range_same_int(s1: Seq<int>, s2: Seq<int>, v: int, start: int, end: int)
        requires
            start <= end,
            forall |i: int| start <= i < end ==> s1[i] == s2[i]
        ensures Self::count_in_range_int(s1, v, start, end)
            == Self::count_in_range_int(s2, v, start, end)
        decreases end - start
    {
        if start < end {
            Self::count_in_range_same_int(s1, s2, v, start + 1, end);
        }
    }

    proof fn count_int_eq_count_in_range(s: Seq<int>, v: int)
        ensures Self::count_int(s, v) == Self::count_in_range_int(s, v, 0, s.len() as int)
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_int_eq_count_in_range(s.drop_last(), v);
            Self::count_in_range_additive_int(s, v, 0, s.len() as int - 1, s.len() as int);
            Self::count_in_range_same_int(s.drop_last(), s, v, 0, s.len() as int - 1);
            assert(Self::count_in_range_int(s, v, s.len() as int, s.len() as int) == 0);
        }
    }

    proof fn swap_perm_int(c: Seq<int>, a: Seq<int>, i: int, j: int)
        requires
            Self::is_perm_int(c, a),
            0 <= i < c.len(),
            0 <= j < c.len(),
        ensures
            Self::is_perm_int(c.update(i, c[j]).update(j, c[i]), a)
    {
        let c_prime = c.update(i, c[j]).update(j, c[i]);
        if i == j {
            assert(c_prime =~= c);
        } else {
            let n = c.len() as int;
            let lo = if i < j { i } else { j };
            let hi = if i < j { j } else { i };
            assert forall |v: int| Self::count_int(c_prime, v) == Self::count_int(a, v) by {
                Self::count_int_eq_count_in_range(c, v);
                Self::count_int_eq_count_in_range(c_prime, v);
                Self::count_in_range_additive_int(c, v, 0, lo, lo + 1);
                Self::count_in_range_additive_int(c, v, 0, lo + 1, hi);
                Self::count_in_range_additive_int(c, v, 0, hi, hi + 1);
                Self::count_in_range_additive_int(c, v, 0, hi + 1, n);
                Self::count_in_range_additive_int(c_prime, v, 0, lo, lo + 1);
                Self::count_in_range_additive_int(c_prime, v, 0, lo + 1, hi);
                Self::count_in_range_additive_int(c_prime, v, 0, hi, hi + 1);
                Self::count_in_range_additive_int(c_prime, v, 0, hi + 1, n);
                Self::count_in_range_same_int(c, c_prime, v, 0, lo);
                Self::count_in_range_same_int(c, c_prime, v, lo + 1, hi);
                Self::count_in_range_same_int(c, c_prime, v, hi + 1, n);
                assert(Self::count_in_range_int(c, v, 0, lo)
                    == Self::count_in_range_int(c_prime, v, 0, lo));
                assert(Self::count_in_range_int(c, v, lo + 1, hi)
                    == Self::count_in_range_int(c_prime, v, lo + 1, hi));
                assert(Self::count_in_range_int(c, v, hi + 1, n)
                    == Self::count_in_range_int(c_prime, v, hi + 1, n));
                assert(Self::count_in_range_int(c, v, 0, n)
                    == Self::count_in_range_int(c, v, 0, lo)
                        + Self::count_in_range_int(c, v, lo, lo + 1)
                        + Self::count_in_range_int(c, v, lo + 1, hi)
                        + Self::count_in_range_int(c, v, hi, hi + 1)
                        + Self::count_in_range_int(c, v, hi + 1, n));
                assert(Self::count_in_range_int(c_prime, v, 0, n)
                    == Self::count_in_range_int(c_prime, v, 0, lo)
                        + Self::count_in_range_int(c_prime, v, lo, lo + 1)
                        + Self::count_in_range_int(c_prime, v, lo + 1, hi)
                        + Self::count_in_range_int(c_prime, v, hi, hi + 1)
                        + Self::count_in_range_int(c_prime, v, hi + 1, n));
                assert(Self::count_in_range_int(c, v, lo + 1, lo + 1) == 0);
                assert(Self::count_in_range_int(c, v, hi + 1, hi + 1) == 0);
                assert(Self::count_in_range_int(c_prime, v, lo + 1, lo + 1) == 0);
                assert(Self::count_in_range_int(c_prime, v, hi + 1, hi + 1) == 0);
            };
        }
    }

    proof fn drop_last_perm_int(c: Seq<int>, a: Seq<int>)
        requires
            Self::is_perm_int(c, a),
            c.len() > 0,
            c.last() == a.last(),
        ensures
            Self::is_perm_int(c.drop_last(), a.drop_last())
    {
        assert forall |v: int| Self::count_int(c.drop_last(), v)
            == Self::count_int(a.drop_last(), v) by {
            Self::count_int_nonneg(c.drop_last(), v);
            Self::count_int_nonneg(a.drop_last(), v);
            assert(Self::count_int(c, v)
                == (if c.last() == v { 1int } else { 0int })
                    + Self::count_int(c.drop_last(), v));
            assert(Self::count_int(a, v)
                == (if a.last() == v { 1int } else { 0int })
                    + Self::count_int(a.drop_last(), v));
        };
    }

    proof fn dot_product_drop_last_helper(a: Seq<int>, b: Seq<int>, k: int)
        requires
            a.len() > 0,
            a.len() == b.len(),
            0 <= k,
        ensures
            Self::dot_product_int(a, b, k)
                == Self::dot_product_int(a.drop_last(), b.drop_last(), k)
                    + if k < a.len() as int { a.last() * b.last() } else { 0int }
        decreases a.len() - k
    {
        if k >= a.len() as int {
        } else if k == a.len() as int - 1 {
            assert(a.last() == a[k]);
            assert(b.last() == b[k]);
            assert(a[k] * b[k] == a.last() * b.last()) by(nonlinear_arith)
                requires a.last() == a[k], b.last() == b[k];
            assert(Self::dot_product_int(a, b, k + 1) == 0);
            assert(Self::dot_product_int(a.drop_last(), b.drop_last(), k) == 0);
        } else {
            assert(a.drop_last()[k] == a[k]);
            assert(b.drop_last()[k] == b[k]);
            assert(a.drop_last()[k] * b.drop_last()[k] == a[k] * b[k]) by(nonlinear_arith)
                requires a.drop_last()[k] == a[k], b.drop_last()[k] == b[k];
            Self::dot_product_drop_last_helper(a, b, k + 1);
        }
    }

    proof fn dot_product_drop_last_int(a: Seq<int>, b: Seq<int>)
        requires a.len() > 0, a.len() == b.len()
        ensures Self::dot_product_int(a, b, 0)
                == Self::dot_product_int(a.drop_last(), b.drop_last(), 0) + a.last() * b.last()
    {
        Self::dot_product_drop_last_helper(a, b, 0);
    }

    proof fn dot_product_update_int(s: Seq<int>, t: Seq<int>, pos: int, val: int, start: int)
        requires s.len() == t.len(), 0 <= pos < s.len(), 0 <= start
        ensures Self::dot_product_int(s.update(pos, val), t, start)
                == Self::dot_product_int(s, t, start)
                    + if start <= pos { (val - s[pos]) * t[pos] } else { 0int }
        decreases s.len() - start
    {
        if start >= s.len() as int {
        } else {
            if start == pos {
                assert(val * t[start]
                    == s[start] * t[start] + (val - s[start]) * t[start]) by(nonlinear_arith);
            }
            Self::dot_product_update_int(s, t, pos, val, start + 1);
        }
    }

    proof fn element_has_positive_count(s: Seq<int>, k: int)
        requires 0 <= k < s.len()
        ensures Self::count_int(s, s[k]) >= 1
        decreases s.len()
    {
        Self::count_int_nonneg(s.drop_last(), s[k]);
        if k < s.len() as int - 1 {
            Self::element_has_positive_count(s.drop_last(), k);
        }
    }

    proof fn perm_max(a: Seq<int>, c: Seq<int>)
        requires Self::is_sorted_int(a), Self::is_perm_int(c, a), a.len() > 0
        ensures forall |k: int| 0 <= k < a.len() ==> c[k] <= a.last()
    {
        assert forall |k: int| 0 <= k < a.len() implies c[k] <= a.last() by {
            Self::element_has_positive_count(c, k);
            if c[k] > a.last() {
                Self::count_int_positive_exists(a, c[k]);
            }
        };
    }

    proof fn rearrangement_ineq(a: Seq<int>, b: Seq<int>, c: Seq<int>)
        requires
            a.len() == b.len(), a.len() == c.len(),
            Self::is_sorted_int(a), Self::is_sorted_int(b),
            Self::is_perm_int(c, a),
        ensures Self::dot_product_int(a, b, 0) >= Self::dot_product_int(c, b, 0)
        decreases a.len()
    {
        if a.len() == 0 {
            assert(Self::dot_product_int(a, b, 0) == 0);
            assert(Self::dot_product_int(c, b, 0) == 0);
        } else if a.len() == 1 {
            Self::element_has_positive_count(a, 0);
            assert(Self::count_int(c, a[0]) >= 1);
            Self::count_int_positive_exists(c, a[0]);
            let w = choose |w: int| 0 <= w < c.len() && c[w] == a[0];
            assert(c[0] == a[0]);
            assert(a[0] * b[0] == c[0] * b[0]) by(nonlinear_arith)
                requires a[0] == c[0];
            assert(Self::dot_product_int(a, b, 1) == 0);
            assert(Self::dot_product_int(c, b, 1) == 0);
            assert(Self::dot_product_int(a, b, 0) == a[0] * b[0]);
            assert(Self::dot_product_int(c, b, 0) == c[0] * b[0]);
        } else {
            let n = a.len() as int;
            Self::count_int_nonneg(c, a.last());
            assert(Self::count_int(c, a.last()) >= 1) by {
                assert(Self::count_int(a, a.last()) >= 1) by {
                    Self::count_int_nonneg(a.drop_last(), a.last());
                };
            };
            Self::count_int_positive_exists(c, a.last());
            let k = choose |k: int| 0 <= k < n && c[k] == a.last();
            if k == n - 1 {
                Self::drop_last_perm_int(c, a);
                Self::dot_product_drop_last_int(a, b);
                Self::dot_product_drop_last_int(c, b);
                Self::rearrangement_ineq(a.drop_last(), b.drop_last(), c.drop_last());
                assert(a.last() * b.last() == c.last() * b.last()) by(nonlinear_arith)
                    requires c.last() == a.last();
                assert(Self::dot_product_int(a.drop_last(), b.drop_last(), 0)
                    >= Self::dot_product_int(c.drop_last(), b.drop_last(), 0));
                assert(Self::dot_product_int(a, b, 0) ==
                    Self::dot_product_int(a.drop_last(), b.drop_last(), 0) + a.last() * b.last());
                assert(Self::dot_product_int(c, b, 0) ==
                    Self::dot_product_int(c.drop_last(), b.drop_last(), 0) + c.last() * b.last());
                assert(Self::dot_product_int(a, b, 0) >= Self::dot_product_int(c, b, 0));
            } else {
                let c_prime = c.update(k, c[n - 1]).update(n - 1, c[k]);
                Self::dot_product_update_int(c, b, k, c[n - 1], 0);
                Self::dot_product_update_int(c.update(k, c[n - 1]), b, n - 1, c[k], 0);
                Self::perm_max(a, c);
                assert(c[n - 1] <= a[n - 1]);
                assert(c[k] == a[n - 1]);
                assert(b[n - 1] >= b[k]);
                assert((a[n - 1] - c[n - 1]) * (b[n - 1] - b[k]) >= 0) by(nonlinear_arith)
                    requires a[n - 1] >= c[n - 1], b[n - 1] >= b[k];
                assert(Self::dot_product_int(c_prime, b, 0) >= Self::dot_product_int(c, b, 0)) by {
                    assert(Self::dot_product_int(c_prime, b, 0)
                        == Self::dot_product_int(c, b, 0)
                            + (c[n - 1] - c[k]) * b[k]
                            + (c[k] - c.update(k, c[n - 1])[n - 1]) * b[n - 1]);
                    assert(c.update(k, c[n - 1])[n - 1] == c[n - 1]);
                    assert(Self::dot_product_int(c_prime, b, 0)
                        == Self::dot_product_int(c, b, 0)
                            + (c[n - 1] - a[n - 1]) * b[k]
                            + (a[n - 1] - c[n - 1]) * b[n - 1]);
                    assert((c[n - 1] - a[n - 1]) * b[k] + (a[n - 1] - c[n - 1]) * b[n - 1]
                        == (a[n - 1] - c[n - 1]) * (b[n - 1] - b[k])) by(nonlinear_arith);
                    assert((a[n - 1] - c[n - 1]) * (b[n - 1] - b[k]) >= 0) by(nonlinear_arith)
                        requires a[n - 1] >= c[n - 1], b[n - 1] >= b[k];
                };
                Self::swap_perm_int(c, a, k, n - 1);
                assert(c_prime.last() == a.last());
                Self::drop_last_perm_int(c_prime, a);
                Self::dot_product_drop_last_int(a, b);
                Self::dot_product_drop_last_int(c_prime, b);
                Self::rearrangement_ineq(a.drop_last(), b.drop_last(), c_prime.drop_last());
                assert(a.last() * b.last() == c_prime.last() * b.last()) by(nonlinear_arith)
                    requires c_prime.last() == a.last();
                assert(Self::dot_product_int(a.drop_last(), b.drop_last(), 0)
                    >= Self::dot_product_int(c_prime.drop_last(), b.drop_last(), 0));
                assert(Self::dot_product_int(a, b, 0) ==
                    Self::dot_product_int(a.drop_last(), b.drop_last(), 0) + a.last() * b.last());
                assert(Self::dot_product_int(c_prime, b, 0) ==
                    Self::dot_product_int(c_prime.drop_last(), b.drop_last(), 0) + c_prime.last() * b.last());
                assert(Self::dot_product_int(a, b, 0) >= Self::dot_product_int(c_prime, b, 0));
                assert(Self::dot_product_int(c_prime, b, 0) >= Self::dot_product_int(c, b, 0));
                assert(Self::dot_product_int(a, b, 0) >= Self::dot_product_int(c, b, 0));
            }
        }
    }

    proof fn dot_product_nonneg(a: Seq<int>, b: Seq<int>, k: int)
        requires
            a.len() == b.len(),
            forall |i: int| 0 <= i < a.len() ==> a[i] >= 0,
            forall |i: int| 0 <= i < b.len() ==> b[i] >= 0,
            0 <= k,
        ensures Self::dot_product_int(a, b, k) >= 0
        decreases a.len() - k
    {
        if k < a.len() as int {
            Self::dot_product_nonneg(a, b, k + 1);
        }
    }

    proof fn mod_add_lemma(x: int, y: int, m: int)
        requires m > 0, 0 <= x < m, 0 <= y
        ensures (x + y) % m >= 0, (x + y) % m < m
    {}

    

    proof fn count_occ_nonneg(s: Seq<i32>, val: i32)
        ensures Self::count_occ(s, val) >= 0
        decreases s.len()
    {
        if s.len() > 0 { Self::count_occ_nonneg(s.drop_last(), val); }
    }

    proof fn count_occ_push(s: Seq<i32>, val: i32, query: i32)
        ensures Self::count_occ(s.push(val), query)
            == Self::count_occ(s, query) + if val == query { 1int } else { 0int }
    {
        assert(s.push(val).drop_last() =~= s);
    }

    proof fn count_occ_append(a: Seq<i32>, b: Seq<i32>, val: i32)
        ensures Self::count_occ(a + b, val)
            == Self::count_occ(a, val) + Self::count_occ(b, val)
        decreases b.len()
    {
        if b.len() == 0 {
            assert(a + b =~= a);
        } else {
            assert((a + b).drop_last() =~= a + b.drop_last());
            Self::count_occ_append(a, b.drop_last(), val);
        }
    }

    proof fn count_occ_contains(s: Seq<i32>, idx: int)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, s[idx]) >= 1
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), s[idx]);
        if idx < s.len() - 1 {
            Self::count_occ_contains(s.drop_last(), idx);
        }
    }

    proof fn find_occ_pos(s: Seq<i32>, val: i32) -> (pos: int)
        requires Self::count_occ(s, val) >= 1
        ensures 0 <= pos < s.len(), s[pos] == val
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), val);
        if s.last() == val { (s.len() - 1) as int }
        else { Self::find_occ_pos(s.drop_last(), val) }
    }

    proof fn perm_refl(s: Seq<i32>)
        ensures Self::is_perm(s, s)
    {}

    proof fn perm_trans(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
        requires Self::is_perm(a, b), Self::is_perm(b, c)
        ensures Self::is_perm(a, c)
    {}

    proof fn perm_append(a1: Seq<i32>, a2: Seq<i32>, b1: Seq<i32>, b2: Seq<i32>)
        requires Self::is_perm(a1, b1), Self::is_perm(a2, b2)
        ensures Self::is_perm(a1 + a2, b1 + b2)
    {
        assert forall |v: i32|
            Self::count_occ(a1 + a2, v) == Self::count_occ(b1 + b2, v) by {
            Self::count_occ_append(a1, a2, v);
            Self::count_occ_append(b1, b2, v);
        };
    }

    proof fn perm_preserves_bounds(a: Seq<i32>, b: Seq<i32>, lo: i32, hi: i32)
        requires
            Self::is_perm(a, b),
            forall |i: int| 0 <= i < b.len() ==> lo <= #[trigger] b[i] <= hi,
        ensures
            forall |i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] <= hi,
    {
        assert forall |i: int| 0 <= i < a.len()
            implies lo <= #[trigger] a[i] <= hi by {
            Self::count_occ_contains(a, i);
            let _ = Self::find_occ_pos(b, a[i]);
        };
    }

    

    proof fn count_occ_i64_nonneg(s: Seq<i64>, val: i64)
        ensures Self::count_occ_i64(s, val) >= 0
        decreases s.len()
    {
        if s.len() > 0 { Self::count_occ_i64_nonneg(s.drop_last(), val); }
    }

    proof fn count_occ_i64_push(s: Seq<i64>, val: i64, query: i64)
        ensures Self::count_occ_i64(s.push(val), query)
            == Self::count_occ_i64(s, query) + if val == query { 1int } else { 0int }
    {
        assert(s.push(val).drop_last() =~= s);
    }

    proof fn count_occ_i64_append(a: Seq<i64>, b: Seq<i64>, val: i64)
        ensures Self::count_occ_i64(a + b, val)
            == Self::count_occ_i64(a, val) + Self::count_occ_i64(b, val)
        decreases b.len()
    {
        if b.len() == 0 {
            assert(a + b =~= a);
        } else {
            assert((a + b).drop_last() =~= a + b.drop_last());
            Self::count_occ_i64_append(a, b.drop_last(), val);
        }
    }

    proof fn count_occ_i64_contains(s: Seq<i64>, idx: int)
        requires 0 <= idx < s.len()
        ensures Self::count_occ_i64(s, s[idx]) >= 1
        decreases s.len()
    {
        Self::count_occ_i64_nonneg(s.drop_last(), s[idx]);
        if idx < s.len() - 1 {
            Self::count_occ_i64_contains(s.drop_last(), idx);
        }
    }

    proof fn find_occ_pos_i64(s: Seq<i64>, val: i64) -> (pos: int)
        requires Self::count_occ_i64(s, val) >= 1
        ensures 0 <= pos < s.len(), s[pos] == val
        decreases s.len()
    {
        Self::count_occ_i64_nonneg(s.drop_last(), val);
        if s.last() == val { (s.len() - 1) as int }
        else { Self::find_occ_pos_i64(s.drop_last(), val) }
    }

    proof fn perm_i64_refl(s: Seq<i64>)
        ensures Self::is_perm_i64(s, s)
    {}

    proof fn perm_i64_trans(a: Seq<i64>, b: Seq<i64>, c: Seq<i64>)
        requires Self::is_perm_i64(a, b), Self::is_perm_i64(b, c)
        ensures Self::is_perm_i64(a, c)
    {}

    proof fn perm_i64_append(a1: Seq<i64>, a2: Seq<i64>, b1: Seq<i64>, b2: Seq<i64>)
        requires Self::is_perm_i64(a1, b1), Self::is_perm_i64(a2, b2)
        ensures Self::is_perm_i64(a1 + a2, b1 + b2)
    {
        assert forall |v: i64|
            Self::count_occ_i64(a1 + a2, v) == Self::count_occ_i64(b1 + b2, v) by {
            Self::count_occ_i64_append(a1, a2, v);
            Self::count_occ_i64_append(b1, b2, v);
        };
    }

    proof fn perm_i64_preserves_bounds(a: Seq<i64>, b: Seq<i64>, lo: i64, hi: i64)
        requires
            Self::is_perm_i64(a, b),
            forall |i: int| 0 <= i < b.len() ==> lo <= #[trigger] b[i] <= hi,
        ensures
            forall |i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] <= hi,
    {
        assert forall |i: int| 0 <= i < a.len()
            implies lo <= #[trigger] a[i] <= hi by {
            Self::count_occ_i64_contains(a, i);
            let _ = Self::find_occ_pos_i64(b, a[i]);
        };
    }

    

    proof fn count_relates_i32(s: Seq<i32>, v: int)
        ensures Self::count_int(Self::to_int_seq(s), v) ==
            (if i32::MIN as int <= v <= i32::MAX as int {
                Self::count_occ(s, v as i32)
            } else { 0int })
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_relates_i32(s.drop_last(), v);
            assert(Self::to_int_seq(s).drop_last() =~= Self::to_int_seq(s.drop_last()));
        }
    }

    proof fn perm_implies_perm_int(a: Seq<i32>, b: Seq<i32>)
        requires Self::is_perm(a, b)
        ensures Self::is_perm_int(Self::to_int_seq(a), Self::to_int_seq(b))
    {
        assert forall |v: int|
            Self::count_int(Self::to_int_seq(a), v)
            == Self::count_int(Self::to_int_seq(b), v)
        by {
            Self::count_relates_i32(a, v);
            Self::count_relates_i32(b, v);
        };
    }

    proof fn count_relates_i64(s: Seq<i64>, v: int)
        ensures Self::count_int(Self::to_int_seq_i64(s), v) ==
            (if i64::MIN as int <= v <= i64::MAX as int {
                Self::count_occ_i64(s, v as i64)
            } else { 0int })
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_relates_i64(s.drop_last(), v);
            assert(Self::to_int_seq_i64(s).drop_last() =~= Self::to_int_seq_i64(s.drop_last()));
        }
    }

    proof fn perm_i64_implies_perm_int(a: Seq<i64>, b: Seq<i64>)
        requires Self::is_perm_i64(a, b)
        ensures Self::is_perm_int(Self::to_int_seq_i64(a), Self::to_int_seq_i64(b))
    {
        assert forall |v: int|
            Self::count_int(Self::to_int_seq_i64(a), v)
            == Self::count_int(Self::to_int_seq_i64(b), v)
        by {
            Self::count_relates_i64(a, v);
            Self::count_relates_i64(b, v);
        };
    }

    

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
            invariant
                0 <= i <= a.len(), 0 <= j <= b.len(),
                Self::is_sorted(a@), Self::is_sorted(b@),
                Self::is_sorted(result@),
                result@.len() == i + j,
                Self::is_perm(result@,
                    a@.subrange(0, i as int) + b@.subrange(0, j as int)),
                i < a.len() ==> (forall |k: int|
                    0 <= k < result@.len() ==> result[k] <= a[i as int]),
                j < b.len() ==> (forall |k: int|
                    0 <= k < result@.len() ==> result[k] <= b[j as int]),
            decreases a.len() - i + b.len() - j,
        {
            let ghost old_result = result@;
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                proof {
                    assert(Self::is_sorted(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q] by {
                            if q < old_result.len() as int {
                            } else if p < old_result.len() as int {
                                assert(result[q] == a[i as int]);
                            }
                        };
                    };
                    let new_a_prefix = a@.subrange(0, (i + 1) as int);
                    let old_a_prefix = a@.subrange(0, i as int);
                    let b_prefix = b@.subrange(0, j as int);
                    assert(new_a_prefix =~= old_a_prefix.push(a[i as int]));
                    assert(result@ =~= old_result.push(a[i as int]));
                    assert forall |v: i32|
                        Self::count_occ(result@, v)
                        == Self::count_occ(new_a_prefix + b_prefix, v) by {
                        Self::count_occ_push(old_result, a[i as int], v);
                        Self::count_occ_append(new_a_prefix, b_prefix, v);
                        Self::count_occ_push(old_a_prefix, a[i as int], v);
                        Self::count_occ_append(old_a_prefix, b_prefix, v);
                    };
                }
                i = i + 1;
            } else {
                result.push(b[j]);
                proof {
                    assert(Self::is_sorted(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q] by {
                            if q < old_result.len() as int {
                            } else if p < old_result.len() as int {
                                assert(result[q] == b[j as int]);
                            }
                        };
                    };
                    let a_prefix = a@.subrange(0, i as int);
                    let new_b_prefix = b@.subrange(0, (j + 1) as int);
                    let old_b_prefix = b@.subrange(0, j as int);
                    assert(new_b_prefix =~= old_b_prefix.push(b[j as int]));
                    assert(result@ =~= old_result.push(b[j as int]));
                    assert forall |v: i32|
                        Self::count_occ(result@, v)
                        == Self::count_occ(a_prefix + new_b_prefix, v) by {
                        Self::count_occ_push(old_result, b[j as int], v);
                        Self::count_occ_append(a_prefix, new_b_prefix, v);
                        Self::count_occ_push(old_b_prefix, b[j as int], v);
                        Self::count_occ_append(a_prefix, old_b_prefix, v);
                    };
                }
                j = j + 1;
            }
        }
        proof {
            assert(a@.subrange(0, a@.len() as int) =~= a@);
            assert(b@.subrange(0, b@.len() as int) =~= b@);
        }
        result
    }

    fn ms_sort(input: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted(result@),
            result@.len() == input@.len(),
            Self::is_perm(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
                proof { assert(result@ =~= input@); Self::perm_refl(input@); }
            } else {
                proof { assert(result@ =~= input@); Self::perm_refl(input@); }
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant
                0 <= i <= mid, mid <= n, n == input.len(),
                left.len() == i,
                forall |k: int| 0 <= k < i as int ==> left[k] == input[k],
            decreases mid - i,
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
            invariant
                mid <= j <= n, n == input.len(),
                right.len() == j - mid,
                forall |k: int| 0 <= k < (j - mid) as int
                    ==> right[k] == input[k + mid as int],
            decreases n - j,
        {
            right.push(input[j]);
            j = j + 1;
        }
        proof {
            assert(left@ =~= input@.subrange(0, mid as int));
            assert(right@ =~= input@.subrange(mid as int, n as int));
            assert(input@ =~= left@ + right@);
            Self::perm_refl(input@);
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        proof {
            Self::perm_append(sorted_left@, sorted_right@, left@, right@);
            Self::perm_trans(result@, sorted_left@ + sorted_right@, left@ + right@);
            assert(left@ + right@ =~= input@);
        }
        result
    }

    

    fn ms_merge_i64(a: &Vec<i64>, b: &Vec<i64>) -> (result: Vec<i64>)
        requires Self::is_sorted_i64(a@), Self::is_sorted_i64(b@)
        ensures
            Self::is_sorted_i64(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm_i64(result@, a@ + b@),
    {
        let mut result: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
            invariant
                0 <= i <= a.len(), 0 <= j <= b.len(),
                Self::is_sorted_i64(a@), Self::is_sorted_i64(b@),
                Self::is_sorted_i64(result@),
                result@.len() == i + j,
                Self::is_perm_i64(result@,
                    a@.subrange(0, i as int) + b@.subrange(0, j as int)),
                i < a.len() ==> (forall |k: int|
                    0 <= k < result@.len() ==> result[k] <= a[i as int]),
                j < b.len() ==> (forall |k: int|
                    0 <= k < result@.len() ==> result[k] <= b[j as int]),
            decreases a.len() - i + b.len() - j,
        {
            let ghost old_result = result@;
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                proof {
                    assert(Self::is_sorted_i64(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q] by {
                            if q < old_result.len() as int {
                            } else if p < old_result.len() as int {
                                assert(result[q] == a[i as int]);
                            }
                        };
                    };
                    let new_a_prefix = a@.subrange(0, (i + 1) as int);
                    let old_a_prefix = a@.subrange(0, i as int);
                    let b_prefix = b@.subrange(0, j as int);
                    assert(new_a_prefix =~= old_a_prefix.push(a[i as int]));
                    assert(result@ =~= old_result.push(a[i as int]));
                    assert forall |v: i64|
                        Self::count_occ_i64(result@, v)
                        == Self::count_occ_i64(new_a_prefix + b_prefix, v) by {
                        Self::count_occ_i64_push(old_result, a[i as int], v);
                        Self::count_occ_i64_append(new_a_prefix, b_prefix, v);
                        Self::count_occ_i64_push(old_a_prefix, a[i as int], v);
                        Self::count_occ_i64_append(old_a_prefix, b_prefix, v);
                    };
                }
                i = i + 1;
            } else {
                result.push(b[j]);
                proof {
                    assert(Self::is_sorted_i64(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q] by {
                            if q < old_result.len() as int {
                            } else if p < old_result.len() as int {
                                assert(result[q] == b[j as int]);
                            }
                        };
                    };
                    let a_prefix = a@.subrange(0, i as int);
                    let new_b_prefix = b@.subrange(0, (j + 1) as int);
                    let old_b_prefix = b@.subrange(0, j as int);
                    assert(new_b_prefix =~= old_b_prefix.push(b[j as int]));
                    assert(result@ =~= old_result.push(b[j as int]));
                    assert forall |v: i64|
                        Self::count_occ_i64(result@, v)
                        == Self::count_occ_i64(a_prefix + new_b_prefix, v) by {
                        Self::count_occ_i64_push(old_result, b[j as int], v);
                        Self::count_occ_i64_append(a_prefix, new_b_prefix, v);
                        Self::count_occ_i64_push(old_b_prefix, b[j as int], v);
                        Self::count_occ_i64_append(a_prefix, old_b_prefix, v);
                    };
                }
                j = j + 1;
            }
        }
        proof {
            assert(a@.subrange(0, a@.len() as int) =~= a@);
            assert(b@.subrange(0, b@.len() as int) =~= b@);
        }
        result
    }

    fn ms_sort_i64(input: &Vec<i64>) -> (result: Vec<i64>)
        ensures
            Self::is_sorted_i64(result@),
            result@.len() == input@.len(),
            Self::is_perm_i64(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
                proof { assert(result@ =~= input@); Self::perm_i64_refl(input@); }
            } else {
                proof { assert(result@ =~= input@); Self::perm_i64_refl(input@); }
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant
                0 <= i <= mid, mid <= n, n == input.len(),
                left.len() == i,
                forall |k: int| 0 <= k < i as int ==> left[k] == input[k],
            decreases mid - i,
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut j: usize = mid;
        while j < n
            invariant
                mid <= j <= n, n == input.len(),
                right.len() == j - mid,
                forall |k: int| 0 <= k < (j - mid) as int
                    ==> right[k] == input[k + mid as int],
            decreases n - j,
        {
            right.push(input[j]);
            j = j + 1;
        }
        proof {
            assert(left@ =~= input@.subrange(0, mid as int));
            assert(right@ =~= input@.subrange(mid as int, n as int));
            assert(input@ =~= left@ + right@);
            Self::perm_i64_refl(input@);
        }
        let sorted_left = Self::ms_sort_i64(&left);
        let sorted_right = Self::ms_sort_i64(&right);
        let result = Self::ms_merge_i64(&sorted_left, &sorted_right);
        proof {
            Self::perm_i64_append(sorted_left@, sorted_right@, left@, right@);
            Self::perm_i64_trans(result@, sorted_left@ + sorted_right@, left@ + right@);
            assert(left@ + right@ =~= input@);
        }
        result
    }

    

    pub fn max_sum_range_query(nums: Vec<i32>, requests: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==>
                0 <= #[trigger] nums@[i] <= 100_000,
            1 <= requests@.len() <= 100_000,
            forall |i: int| 0 <= i < requests@.len() ==> (
                (#[trigger] requests@[i])@.len() == 2
                    && 0 <= requests@[i]@[0]
                    && requests@[i]@[0] <= requests@[i]@[1]
                    && (requests@[i]@[1] as int) < nums@.len() as int
            ),
        ensures
            0 <= result < 1_000_000_007,
            exists |sv: Seq<int>, sf: Seq<int>|
                sv.len() == nums@.len()
                && sf.len() == nums@.len()
                && Self::is_sorted_int(sv)
                && Self::is_sorted_int(sf)
                && Self::is_perm_int(sv, Self::to_int_seq(nums@))
                && Self::is_perm_int(sf, Self::freq_vec(requests@, nums@.len() as int))
                && result as int
                    == Self::dot_product_int(sv, sf, 0) % 1_000_000_007
                && forall |c: Seq<int>|
                    c.len() == sv.len() && Self::is_perm_int(c, sv)
                        ==> Self::dot_product_int(sv, sf, 0)
                            >= Self::dot_product_int(c, sf, 0),
    {
        let ghost orig_nums_int = Self::to_int_seq(nums@);
        let n = nums.len();
        let m = requests.len();
        let modval: i64 = 1_000_000_007;

        
        let mut count: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums@.len(),
                m == requests@.len(),
                count@.len() == i as int,
                0 <= i <= n,
                1 <= n <= 100_000,
                1 <= m <= 100_000,
                forall |k: int| 0 <= k < i as int ==>
                    (#[trigger] count@[k]) as int == Self::freq_at(requests@, k, 0),
                forall |k: int| 0 <= k < i as int ==>
                    0 <= #[trigger] count@[k] <= m as i64,
                forall |ii: int| 0 <= ii < nums@.len() ==>
                    0 <= #[trigger] nums@[ii] <= 100_000,
                forall |ii: int| 0 <= ii < requests@.len() ==> (
                    (#[trigger] requests@[ii])@.len() == 2
                        && 0 <= requests@[ii]@[0]
                        && requests@[ii]@[0] <= requests@[ii]@[1]
                        && (requests@[ii]@[1] as int) < nums@.len() as int
                ),
            decreases n - i,
        {
            let mut freq: i64 = 0;
            let mut r: usize = 0;
            while r < m
                invariant
                    n == nums@.len(),
                    m == requests@.len(),
                    0 <= i < n,
                    0 <= r <= m,
                    0 <= freq,
                    freq as int <= r as int,
                    1 <= m <= 100_000,
                    freq as int + Self::freq_at(requests@, i as int, r as int)
                        == Self::freq_at(requests@, i as int, 0),
                    forall |ii: int| 0 <= ii < requests@.len() ==> (
                        (#[trigger] requests@[ii])@.len() == 2
                            && 0 <= requests@[ii]@[0]
                            && requests@[ii]@[0] <= requests@[ii]@[1]
                            && (requests@[ii]@[1] as int) < nums@.len() as int
                    ),
                decreases m - r,
            {
                if requests[r][0] as usize <= i && i <= requests[r][1] as usize {
                    freq = freq + 1;
                }
                r = r + 1;
            }
            count.push(freq);
            i = i + 1;
        }
        proof {
            assert(count@.len() == n as int);
            assert forall |k: int| 0 <= k < n as int implies
                Self::to_int_seq_i64(count@)[k] == Self::freq_vec(requests@, n as int)[k] by {};
            assert(Self::to_int_seq_i64(count@) =~= Self::freq_vec(requests@, n as int));
        }
        let ghost orig_count_int = Self::to_int_seq_i64(count@);

        
        let ghost pre_sort_nums = nums@;
        let nums = Self::ms_sort(&nums);

        
        let sorted_count = Self::ms_sort_i64(&count);

        let ghost sv = Self::to_int_seq(nums@);
        let ghost sf = Self::to_int_seq_i64(sorted_count@);

        proof {
            
            assert(Self::is_sorted_int(sv)) by {
                assert forall |a: int, b: int| 0 <= a <= b < sv.len()
                    implies sv[a] <= sv[b] by {};
            };
            
            assert(Self::is_sorted_int(sf)) by {
                assert forall |a: int, b: int| 0 <= a <= b < sf.len()
                    implies sf[a] <= sf[b] by {};
            };

            
            assert(sv.len() == n as int);
            assert(sf.len() == n as int);

            
            Self::perm_implies_perm_int(nums@, pre_sort_nums);
            assert(Self::to_int_seq(pre_sort_nums) == orig_nums_int);

            
            Self::perm_i64_implies_perm_int(sorted_count@, count@);
            assert(Self::to_int_seq_i64(count@) == orig_count_int);
            assert(orig_count_int =~= Self::freq_vec(requests@, n as int));

            
            Self::perm_preserves_bounds(nums@, pre_sort_nums, 0i32, 100_000i32);
            Self::perm_i64_preserves_bounds(sorted_count@, count@, 0i64, m as i64);

            assert forall |ii: int| 0 <= ii < n as int implies sv[ii] <= 100_000 by {};
            assert forall |ii: int| 0 <= ii < n as int implies sf[ii] <= 100_000 by {
                assert(sorted_count@[ii] <= m as i64);
            };
            assert forall |ii: int| 0 <= ii < n as int
                implies (nums@[ii] as i64 as int) * (#[trigger] sorted_count@[ii] as int) <= 10_000_000_000 by {
                assert(0 <= nums@[ii] as int <= 100_000);
                assert(sv[ii] == nums@[ii] as int);
                assert(sf[ii] == sorted_count@[ii] as int);
                assert(0 <= sf[ii] <= 100_000);
                assert(nums@[ii] as i64 as int == nums@[ii] as int);
                assert((nums@[ii] as i64 as int) * (sorted_count@[ii] as int) <= 10_000_000_000) by(nonlinear_arith)
                    requires 0 <= nums@[ii] as i64 as int <= 100_000, 0 <= sorted_count@[ii] as int <= 100_000;
            };
        }

        
        let mut result: i64 = 0;
        let mut k: usize = 0;
        while k < n
            invariant
                n == nums@.len(),
                n == sorted_count@.len(),
                0 <= k <= n,
                0 <= result < 1_000_000_007,
                modval == 1_000_000_007i64,
                1 <= m <= 100_000,
                sv == Self::to_int_seq(nums@),
                sf == Self::to_int_seq_i64(sorted_count@),
                sv.len() == n as int,
                sf.len() == n as int,
                result as int == (Self::dot_product_int(sv, sf, 0)
                    - Self::dot_product_int(sv, sf, k as int)) % 1_000_000_007,
                Self::dot_product_int(sv, sf, 0)
                    - Self::dot_product_int(sv, sf, k as int) >= 0,
                forall |ii: int| 0 <= ii < n as int ==> #[trigger] sv[ii] >= 0,
                forall |ii: int| 0 <= ii < n as int ==> #[trigger] sf[ii] >= 0,
                forall |ii: int| 0 <= ii < n as int ==> sv[ii] <= 100_000,
                forall |ii: int| 0 <= ii < n as int ==> sf[ii] <= 100_000,
                forall |ii: int| 0 <= ii < n as int ==> 0 <= #[trigger] nums@[ii] <= 100_000,
                forall |ii: int| 0 <= ii < n as int ==> 0 <= #[trigger] sorted_count@[ii] <= m as i64,
                forall |ii: int| 0 <= ii < n as int ==> (nums@[ii] as i64 as int) * (#[trigger] sorted_count@[ii] as int) <= 10_000_000_000,
            decreases n - k,
        {
            proof {
                assert(sv[k as int] >= 0);
                assert(sf[k as int] >= 0);
                assert(sv[k as int] <= 100_000);
                assert(sf[k as int] <= 100_000);
                assert(sv[k as int] * sf[k as int] >= 0) by(nonlinear_arith)
                    requires sv[k as int] >= 0, sf[k as int] >= 0;
                assert(sv[k as int] * sf[k as int] <= 100_000 * 100_000) by(nonlinear_arith)
                    requires 0 <= sv[k as int] <= 100_000, 0 <= sf[k as int] <= 100_000;
                let partial_before = Self::dot_product_int(sv, sf, 0)
                    - Self::dot_product_int(sv, sf, k as int);
                let term = sv[k as int] * sf[k as int];
                assert(term >= 0);
                assert(term <= 10_000_000_000);
                assert(Self::dot_product_int(sv, sf, k as int) == term + Self::dot_product_int(sv, sf, k as int + 1));
                Self::dot_product_nonneg(sv, sf, k as int + 1);
                assert(sv[k as int] == nums@[k as int] as int);
                assert(sf[k as int] == sorted_count@[k as int] as int);
                assert(nums@[k as int] as i64 as int == sv[k as int]);
                assert(0 <= (nums@[k as int] as i64 as int) * (sorted_count@[k as int] as int)) by(nonlinear_arith)
                    requires nums@[k as int] as i64 as int >= 0, sorted_count@[k as int] as int >= 0;
                assert((nums@[k as int] as i64 as int) * (sorted_count@[k as int] as int) <= 10_000_000_000) by(nonlinear_arith)
                    requires 0 <= nums@[k as int] as i64 as int <= 100_000,
                             0 <= sorted_count@[k as int] as int <= 100_000;
                assert(result as int + (nums@[k as int] as i64 as int) * (sorted_count@[k as int] as int) >= 0);
                assert(result as int + (nums@[k as int] as i64 as int) * (sorted_count@[k as int] as int) <= 11_000_000_006);
                assert((nums@[k as int] as i64 as int) * (sorted_count@[k as int] as int) <= i64::MAX as int);
                assert(result as int + (nums@[k as int] as i64 as int) * (sorted_count@[k as int] as int) <= i64::MAX as int);
                assert(result as int + term
                    == partial_before % 1_000_000_007 + term);
                assert((partial_before % 1_000_000_007 + term) % 1_000_000_007
                    == (partial_before + term) % 1_000_000_007) by(nonlinear_arith)
                    requires 0 <= partial_before % 1_000_000_007 < 1_000_000_007,
                             0 <= term <= 10_000_000_000i64 as int,
                             partial_before >= 0;
            }
            result = (result + nums[k] as i64 * sorted_count[k]) % modval;
            k = k + 1;
        }
        proof {
            assert(Self::dot_product_int(sv, sf, n as int) == 0);
            assert(result as int == Self::dot_product_int(sv, sf, 0) % 1_000_000_007);
            assert forall |c: Seq<int>| c.len() == sv.len() && Self::is_perm_int(c, sv)
                implies Self::dot_product_int(sv, sf, 0) >= Self::dot_product_int(c, sf, 0) by {
                Self::rearrangement_ineq(sv, sf, c);
            };
        }
        result as i32
    }
}

}
