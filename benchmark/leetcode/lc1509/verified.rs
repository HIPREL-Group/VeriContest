use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn num_changes(a: Seq<i32>, b: Seq<i32>) -> int
        decreases a.len(),
    {
        if a.len() == 0 || a.len() != b.len() { 0 }
        else {
            (if a.last() != b.last() { 1int } else { 0int })
                + Self::num_changes(a.drop_last(), b.drop_last())
        }
    }

    pub open spec fn seq_max(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 0 { i32::MIN as int }
        else if s.len() == 1 { s[0] as int }
        else {
            let rest = Self::seq_max(s.drop_last());
            if s.last() as int >= rest { s.last() as int } else { rest }
        }
    }

    pub open spec fn seq_min(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 0 { i32::MAX as int }
        else if s.len() == 1 { s[0] as int }
        else {
            let rest = Self::seq_min(s.drop_last());
            if (s.last() as int) <= rest { s.last() as int } else { rest }
        }
    }

    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn min4(a: int, b: int, c: int, d: int) -> int {
        let m1 = if a <= b { a } else { b };
        let m2 = if c <= d { c } else { d };
        if m1 <= m2 { m1 } else { m2 }
    }

    proof fn seq_max_ge_elem(s: Seq<i32>, k: int)
        requires 0 <= k < s.len()
        ensures Self::seq_max(s) >= s[k] as int
        decreases s.len()
    {
        if s.len() > 1 && k < s.len() - 1 {
            Self::seq_max_ge_elem(s.drop_last(), k);
        }
    }

    proof fn seq_min_le_elem(s: Seq<i32>, k: int)
        requires 0 <= k < s.len()
        ensures Self::seq_min(s) <= s[k] as int
        decreases s.len()
    {
        if s.len() > 1 && k < s.len() - 1 {
            Self::seq_min_le_elem(s.drop_last(), k);
        }
    }

    proof fn seq_max_bounded(s: Seq<i32>, bound: int)
        requires s.len() > 0, forall |i: int| 0 <= i < s.len() ==> s[i] as int <= bound
        ensures Self::seq_max(s) <= bound
        decreases s.len()
    {
        if s.len() > 1 { Self::seq_max_bounded(s.drop_last(), bound); }
    }

    proof fn seq_min_bounded(s: Seq<i32>, bound: int)
        requires s.len() > 0, forall |i: int| 0 <= i < s.len() ==> s[i] as int >= bound
        ensures Self::seq_min(s) >= bound
        decreases s.len()
    {
        if s.len() > 1 { Self::seq_min_bounded(s.drop_last(), bound); }
    }

    proof fn num_changes_nonneg(a: Seq<i32>, b: Seq<i32>)
        ensures Self::num_changes(a, b) >= 0
        decreases a.len()
    {
        if a.len() > 0 && a.len() == b.len() {
            Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        }
    }

    proof fn num_changes_ge_1(a: Seq<i32>, b: Seq<i32>, p: int)
        requires a.len() == b.len(), 0 <= p < a.len(), a[p] != b[p]
        ensures Self::num_changes(a, b) >= 1
        decreases a.len()
    {
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        if p < a.len() as int - 1 {
            Self::num_changes_ge_1(a.drop_last(), b.drop_last(), p);
        }
    }

    proof fn num_changes_ge_2(a: Seq<i32>, b: Seq<i32>, p0: int, p1: int)
        requires a.len() == b.len(), 0 <= p0 < a.len(), 0 <= p1 < a.len(),
            p0 != p1, a[p0] != b[p0], a[p1] != b[p1]
        ensures Self::num_changes(a, b) >= 2
        decreases a.len()
    {
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        let last = a.len() as int - 1;
        if last == p0 || last == p1 {
            let q = if last == p0 { p1 } else { p0 };
            Self::num_changes_ge_1(a.drop_last(), b.drop_last(), q);
        } else {
            Self::num_changes_ge_2(a.drop_last(), b.drop_last(), p0, p1);
        }
    }

    proof fn num_changes_ge_3(a: Seq<i32>, b: Seq<i32>, p0: int, p1: int, p2: int)
        requires a.len() == b.len(), 0 <= p0 < a.len(), 0 <= p1 < a.len(),
            0 <= p2 < a.len(), p0 != p1, p0 != p2, p1 != p2,
            a[p0] != b[p0], a[p1] != b[p1], a[p2] != b[p2]
        ensures Self::num_changes(a, b) >= 3
        decreases a.len()
    {
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        let last = a.len() as int - 1;
        if last == p0 || last == p1 || last == p2 {
            let (q0, q1) = if last == p0 { (p1, p2) }
                else if last == p1 { (p0, p2) } else { (p0, p1) };
            Self::num_changes_ge_2(a.drop_last(), b.drop_last(), q0, q1);
        } else {
            Self::num_changes_ge_3(a.drop_last(), b.drop_last(), p0, p1, p2);
        }
    }

    proof fn num_changes_ge_4(a: Seq<i32>, b: Seq<i32>, p0: int, p1: int, p2: int, p3: int)
        requires a.len() == b.len(), 0 <= p0 < a.len(), 0 <= p1 < a.len(),
            0 <= p2 < a.len(), 0 <= p3 < a.len(),
            p0 != p1, p0 != p2, p0 != p3, p1 != p2, p1 != p3, p2 != p3,
            a[p0] != b[p0], a[p1] != b[p1], a[p2] != b[p2], a[p3] != b[p3]
        ensures Self::num_changes(a, b) >= 4
        decreases a.len()
    {
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        let last = a.len() as int - 1;
        if last == p0 || last == p1 || last == p2 || last == p3 {
            let (q0, q1, q2) = if last == p0 { (p1, p2, p3) }
                else if last == p1 { (p0, p2, p3) }
                else if last == p2 { (p0, p1, p3) }
                else { (p0, p1, p2) };
            Self::num_changes_ge_3(a.drop_last(), b.drop_last(), q0, q1, q2);
        } else {
            Self::num_changes_ge_4(a.drop_last(), b.drop_last(), p0, p1, p2, p3);
        }
    }

    proof fn num_changes_le_3(a: Seq<i32>, b: Seq<i32>, c0: int, c1: int, c2: int)
        requires
            a.len() == b.len(), 0 <= c0 < a.len(), 0 <= c1 < a.len(), 0 <= c2 < a.len(),
            c0 != c1, c0 != c2, c1 != c2,
            forall |p: int| 0 <= p < a.len() && p != c0 && p != c1 && p != c2 ==> a[p] == b[p],
        ensures Self::num_changes(a, b) <= 3
        decreases a.len()
    {
        if a.len() == 0 { return; }
        let last = a.len() as int - 1;
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        if last == c0 || last == c1 || last == c2 {
            let (q0, q1) = if last == c0 { (c1, c2) }
                else if last == c1 { (c0, c2) } else { (c0, c1) };
            assert forall |p: int| 0 <= p < last && p != q0 && p != q1
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_2(a.drop_last(), b.drop_last(), q0, q1);
        } else {
            assert(a.last() == b.last());
            assert forall |p: int| 0 <= p < last && p != c0 && p != c1 && p != c2
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_3(a.drop_last(), b.drop_last(), c0, c1, c2);
        }
    }

    proof fn num_changes_le_2(a: Seq<i32>, b: Seq<i32>, c0: int, c1: int)
        requires
            a.len() == b.len(), 0 <= c0 < a.len(), 0 <= c1 < a.len(), c0 != c1,
            forall |p: int| 0 <= p < a.len() && p != c0 && p != c1 ==> a[p] == b[p],
        ensures Self::num_changes(a, b) <= 2
        decreases a.len()
    {
        if a.len() == 0 { return; }
        let last = a.len() as int - 1;
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        if last == c0 || last == c1 {
            let q = if last == c0 { c1 } else { c0 };
            assert forall |p: int| 0 <= p < last && p != q
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_1(a.drop_last(), b.drop_last(), q);
        } else {
            assert(a.last() == b.last());
            assert forall |p: int| 0 <= p < last && p != c0 && p != c1
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_2(a.drop_last(), b.drop_last(), c0, c1);
        }
    }

    proof fn num_changes_le_1(a: Seq<i32>, b: Seq<i32>, c0: int)
        requires a.len() == b.len(), 0 <= c0 < a.len(),
            forall |p: int| 0 <= p < a.len() && p != c0 ==> a[p] == b[p],
        ensures Self::num_changes(a, b) <= 1
        decreases a.len()
    {
        if a.len() == 0 { return; }
        let last = a.len() as int - 1;
        Self::num_changes_nonneg(a.drop_last(), b.drop_last());
        if last == c0 {
            assert forall |p: int| 0 <= p < last
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_0(a.drop_last(), b.drop_last());
        } else {
            assert(a.last() == b.last());
            assert forall |p: int| 0 <= p < last && p != c0
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_1(a.drop_last(), b.drop_last(), c0);
        }
    }

    proof fn num_changes_le_0(a: Seq<i32>, b: Seq<i32>)
        requires a.len() == b.len(), forall |p: int| 0 <= p < a.len() ==> a[p] == b[p]
        ensures Self::num_changes(a, b) == 0
        decreases a.len()
    {
        if a.len() > 0 {
            assert forall |p: int| 0 <= p < a.len() - 1
                implies a.drop_last()[p] == b.drop_last()[p] by {};
            Self::num_changes_le_0(a.drop_last(), b.drop_last());
        }
    }

    
    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool {
        forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

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
            let ab = a + b;
            assert(ab.drop_last() =~= a + b.drop_last());
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

    proof fn perm_refl(s: Seq<i32>)
        ensures Self::is_permutation(s, s)
    {}

    proof fn perm_trans(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
        requires Self::is_permutation(a, b), Self::is_permutation(b, c)
        ensures Self::is_permutation(a, c)
    {}

    proof fn perm_append(a1: Seq<i32>, a2: Seq<i32>, b1: Seq<i32>, b2: Seq<i32>)
        requires Self::is_permutation(a1, b1), Self::is_permutation(a2, b2)
        ensures Self::is_permutation(a1 + a2, b1 + b2)
    {
        assert forall |v: i32|
            Self::count_occ(a1 + a2, v) == Self::count_occ(b1 + b2, v) by {
            Self::count_occ_append(a1, a2, v);
            Self::count_occ_append(b1, b2, v);
        };
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_permutation(result@, a@ + b@),
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
                Self::is_permutation(result@,
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
            Self::is_permutation(result@, input@),
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

    
    pub open spec fn seq_remove(s: Seq<i32>, idx: int) -> Seq<i32> {
        s.subrange(0, idx) + s.subrange(idx + 1, s.len() as int)
    }

    proof fn seq_remove_index(s: Seq<i32>, idx: int, k: int)
        requires 0 <= idx < s.len(), 0 <= k < s.len() - 1
        ensures Self::seq_remove(s, idx)[k]
            == if k < idx { s[k] } else { s[k + 1] }
    {
        let r = Self::seq_remove(s, idx);
        let left = s.subrange(0, idx);
        let right = s.subrange(idx + 1, s.len() as int);
        assert(r =~= left + right);
        if k < idx { assert(r[k] == left[k]); }
        else { assert(r[k] == right[k - idx]); }
    }

    proof fn count_occ_remove(s: Seq<i32>, idx: int, v: i32)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, v)
            == Self::count_occ(Self::seq_remove(s, idx), v)
                + if s[idx] == v { 1int } else { 0int }
        decreases s.len()
    {
        let n = s.len();
        if idx == n - 1 {
            assert(Self::seq_remove(s, idx) =~= s.drop_last());
        } else {
            Self::count_occ_remove(s.drop_last(), idx, v);
            let inner = Self::seq_remove(s.drop_last(), idx);
            let full_rem = Self::seq_remove(s, idx);
            assert(full_rem =~= inner.push(s[n - 1]));
            Self::count_occ_push(inner, s[n - 1], v);
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

    proof fn perm_to_bijection(sorted: Seq<i32>, original: Seq<i32>)
        -> (result: (Seq<int>, Seq<int>))
        requires
            sorted.len() == original.len(),
            Self::is_permutation(sorted, original),
        ensures ({
            let (perm, inv) = result;
            perm.len() == sorted.len()
            && inv.len() == sorted.len()
            && (forall |k: int| 0 <= k < sorted.len()
                ==> 0 <= #[trigger] perm[k] < sorted.len())
            && (forall |k: int, l: int| 0 <= k < l < sorted.len()
                ==> perm[k] != perm[l])
            && (forall |k: int| 0 <= k < sorted.len()
                ==> sorted[k] == original[#[trigger] perm[k]])
            && (forall |p: int| 0 <= p < sorted.len()
                ==> 0 <= #[trigger] inv[p] < sorted.len())
            && (forall |p: int| 0 <= p < sorted.len()
                ==> perm[#[trigger] inv[p]] == p)
            && (forall |k: int| 0 <= k < sorted.len()
                ==> inv[#[trigger] perm[k]] == k)
        })
        decreases sorted.len()
    {
        let n = sorted.len();
        if n == 0 {
            return (Seq::<int>::empty(), Seq::<int>::empty());
        }

        let val = sorted[n - 1];
        Self::count_occ_nonneg(sorted.drop_last(), val);
        assert(Self::count_occ(sorted, val) >= 1);
        let pos = Self::find_occ_pos(original, val);

        let sorted2 = sorted.drop_last();
        let original2 = Self::seq_remove(original, pos);

        assert forall |v: i32|
            Self::count_occ(sorted2, v) == Self::count_occ(original2, v) by {
            Self::count_occ_remove(original, pos, v);
        };

        let (sub_perm, sub_inv) = Self::perm_to_bijection(sorted2, original2);

        let perm = Seq::new(n as nat, |k: int|
            if k == n - 1 { pos }
            else { let sk = sub_perm[k]; if sk >= pos { sk + 1 } else { sk } }
        );
        let inv = Seq::new(n as nat, |p: int|
            if p == pos { n as int - 1 }
            else { sub_inv[if p > pos { p - 1 } else { p }] }
        );

        assert forall |k: int| 0 <= k < n
            implies 0 <= #[trigger] perm[k] < n by {
            if k != n - 1 { let sk = sub_perm[k]; assert(0 <= sk < n - 1); }
        };

        assert forall |k: int| 0 <= k < n
            implies sorted[k] == original[#[trigger] perm[k]] by {
            if k == n - 1 {
            } else {
                let sk = sub_perm[k];
                assert(sorted2[k] == original2[sk]);
                Self::seq_remove_index(original, pos, sk);
            }
        };

        assert forall |k: int, l: int| 0 <= k < l < n
            implies perm[k] != perm[l] by {
            if l == n - 1 {
                let sk = sub_perm[k]; assert(0 <= sk < n - 1);
            } else if k == n - 1 {
            } else {
                let sk = sub_perm[k]; let sl = sub_perm[l]; assert(sk != sl);
            }
        };

        assert forall |p: int| 0 <= p < n
            implies 0 <= #[trigger] inv[p] < n by {
            if p != pos {
                let up = if p > pos { (p - 1) as int } else { p };
                assert(0 <= up < n - 1);
            }
        };

        assert forall |p: int| 0 <= p < n
            implies perm[#[trigger] inv[p]] == p by {
            if p == pos {
            } else {
                let up = if p > pos { (p - 1) as int } else { p };
                assert(0 <= up < n - 1);
                let si = sub_inv[up];
                assert(sub_perm[si] == up);
                if p > pos {
                    assert(up == p - 1); assert(up >= pos);
                } else {
                    assert(up == p); assert(up < pos);
                }
            }
        };

        assert forall |k: int| 0 <= k < n
            implies inv[#[trigger] perm[k]] == k by {
            if k == n - 1 {
            } else {
                let sk = sub_perm[k];
                let pk = perm[k];
                assert(pk != pos) by {
                    if sk >= pos { assert(pk == sk + 1); }
                    else { assert(pk == sk); }
                };
                let up_pk = if pk > pos { (pk - 1) as int } else { pk };
                assert(up_pk == sk) by {
                    if pk > pos { assert(sk >= pos); assert(pk == sk + 1); }
                    else { assert(sk < pos); assert(pk == sk); }
                };
                assert(inv[pk] == sub_inv[sk]);
            }
        };

        (perm, inv)
    }

    proof fn perm_preserves_bounds(a: Seq<i32>, b: Seq<i32>, lo: int, hi: int)
        requires
            Self::is_permutation(a, b),
            forall |i: int| 0 <= i < b.len() ==> lo <= #[trigger] b[i] as int <= hi,
        ensures
            forall |i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] as int <= hi,
    {
        assert forall |i: int| 0 <= i < a.len()
            implies lo <= #[trigger] a[i] as int <= hi by {
            Self::count_occ_contains(a, i);
            let j = Self::find_occ_pos(b, a[i]);
        };
    }

    pub fn min_difference(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            nums.len() <= 4 ==> res == 0,
            nums.len() > 4 ==> (
                exists |m: Seq<i32>|
                    m.len() == nums.len()
                    && Self::num_changes(nums@, m) <= 3
                    && res as int == Self::seq_max(m) - Self::seq_min(m)
                    && forall |m2: Seq<i32>|
                        m2.len() == nums.len()
                        && Self::num_changes(nums@, m2) <= 3
                        ==> Self::seq_max(m2) - Self::seq_min(m2) >= res as int
            ),
    {
        let n = nums.len();
        if n <= 4 { return 0; }
        let ghost original = nums@;

        let nums = Self::ms_sort(&nums);

        let ghost perm: Seq<int>;
        let ghost inv: Seq<int>;
        proof {
            let (p, i) = Self::perm_to_bijection(nums@, original);
            perm = p;
            inv = i;
            Self::perm_preserves_bounds(nums@, original,
                -1_000_000_000, 1_000_000_000);
        }

        let d1 = nums[n - 1] - nums[3];
        let d2 = nums[n - 2] - nums[2];
        let d3 = nums[n - 3] - nums[1];
        let d4 = nums[n - 4] - nums[0];
        let mut result = d1;
        let mut best_j: Ghost<int> = Ghost(3);
        if d2 < result {
            result = d2;
            proof { best_j@ = 2; }
        }
        if d3 < result {
            result = d3;
            proof { best_j@ = 1; }
        }
        if d4 < result {
            result = d4;
            proof { best_j@ = 0; }
        }

        proof {
            let j = best_j@;
            let nn = n as int;
            let sorted = nums@;
            assert(0 <= j <= 3);
            assert(result as int == sorted[j + nn - 4] as int - sorted[j] as int);
            let lo = sorted[j];
            let hi = sorted[j + nn - 4];

            let (cp0, cp1, cp2) = if j == 0 {
                (perm[nn - 3], perm[nn - 2], perm[nn - 1])
            } else if j == 1 {
                (perm[0], perm[nn - 2], perm[nn - 1])
            } else if j == 2 {
                (perm[0], perm[1], perm[nn - 1])
            } else {
                (perm[0], perm[1], perm[2])
            };
            assert(cp0 != cp1 && cp0 != cp2 && cp1 != cp2);

            let m = Seq::new(nn as nat, |p: int|
                if p == cp0 || p == cp1 || p == cp2 { lo } else { original[p] }
            );

            assert forall |p: int| 0 <= p < nn && p != cp0 && p != cp1 && p != cp2
                implies original[p] == m[p] by {};
            Self::num_changes_le_3(original, m, cp0, cp1, cp2);

            assert forall |p: int| 0 <= p < nn
                implies lo as int <= #[trigger] m[p] as int <= hi as int by {
                if p == cp0 || p == cp1 || p == cp2 {
                    assert(Self::is_sorted(sorted));
                } else {
                    let si = inv[p];
                    assert(perm[si] == p);
                    assert(original[p] == original[perm[si]]);
                    assert(original[perm[si]] == sorted[si]);
                    if j == 0 {
                        assert(si != nn - 3 && si != nn - 2 && si != nn - 1) by {
                            if si == nn - 3 { assert(perm[si] == perm[nn - 3]); assert(p == cp0); }
                            if si == nn - 2 { assert(perm[si] == perm[nn - 2]); assert(p == cp1); }
                            if si == nn - 1 { assert(perm[si] == perm[nn - 1]); assert(p == cp2); }
                        };
                        assert(0 <= si <= nn - 4);
                    } else if j == 1 {
                        assert(si != 0 && si != nn - 2 && si != nn - 1) by {
                            if si == 0 { assert(perm[si] == perm[0]); assert(p == cp0); }
                            if si == nn - 2 { assert(perm[si] == perm[nn - 2]); assert(p == cp1); }
                            if si == nn - 1 { assert(perm[si] == perm[nn - 1]); assert(p == cp2); }
                        };
                        assert(1 <= si <= nn - 3);
                    } else if j == 2 {
                        assert(si != 0 && si != 1 && si != nn - 1) by {
                            if si == 0 { assert(perm[si] == perm[0]); assert(p == cp0); }
                            if si == 1 { assert(perm[si] == perm[1]); assert(p == cp1); }
                            if si == nn - 1 { assert(perm[si] == perm[nn - 1]); assert(p == cp2); }
                        };
                        assert(2 <= si <= nn - 2);
                    } else {
                        assert(si != 0 && si != 1 && si != 2) by {
                            if si == 0 { assert(perm[si] == perm[0]); assert(p == cp0); }
                            if si == 1 { assert(perm[si] == perm[1]); assert(p == cp1); }
                            if si == 2 { assert(perm[si] == perm[2]); assert(p == cp2); }
                        };
                        assert(3 <= si <= nn - 1);
                    }
                    assert(j <= si && si <= j + nn - 4);
                    assert(Self::is_sorted(sorted));
                }
            };

            Self::seq_max_bounded(m, hi as int);
            Self::seq_min_bounded(m, lo as int);

            let ph = perm[j + nn - 4];
            assert(m[ph] == original[ph]) by {
                assert(j + nn - 4 != (if j == 0 { nn - 3 } else if j == 1 { 0 } else if j == 2 { 0 } else { 0 }));
                if ph == cp0 || ph == cp1 || ph == cp2 {
                    if j == 0 { assert(j+nn-4 != nn-3 && j+nn-4 != nn-2 && j+nn-4 != nn-1); }
                    else if j == 1 { assert(j+nn-4 != 0 && j+nn-4 != nn-2 && j+nn-4 != nn-1); }
                    else if j == 2 { assert(j+nn-4 != 0 && j+nn-4 != 1 && j+nn-4 != nn-1); }
                    else { assert(j+nn-4 != 0 && j+nn-4 != 1 && j+nn-4 != 2); }
                }
            };
            assert(m[ph] == sorted[j + nn - 4]);
            Self::seq_max_ge_elem(m, ph);

            let pl = perm[j];
            assert(m[pl] == original[pl]) by {
                if pl == cp0 || pl == cp1 || pl == cp2 {
                    if j == 0 { assert(0 != nn-3 && 0 != nn-2 && 0 != nn-1); }
                    else if j == 1 { assert(1 != 0 && 1 != nn-2 && 1 != nn-1); }
                    else if j == 2 { assert(2 != 0 && 2 != 1 && 2 != nn-1); }
                    else { assert(3 != 0 && 3 != 1 && 3 != 2); }
                }
            };
            assert(m[pl] == sorted[j]);
            Self::seq_min_le_elem(m, pl);

            assert(Self::seq_max(m) == hi as int);
            assert(Self::seq_min(m) == lo as int);

            
            assert forall |m2: Seq<i32>|
                m2.len() == nn && Self::num_changes(original, m2) <= 3
                implies Self::seq_max(m2) - Self::seq_min(m2) >= result as int
            by {
                let bot_si: int = if m2[perm[0]] == original[perm[0]] { 0 }
                    else if m2[perm[1]] == original[perm[1]] { 1 }
                    else if m2[perm[2]] == original[perm[2]] { 2 }
                    else {
                        if m2[perm[3]] != original[perm[3]] {
                            Self::num_changes_ge_4(original, m2, perm[0], perm[1], perm[2], perm[3]);
                        }
                        3
                    };
                assert(m2[perm[bot_si]] == original[perm[bot_si]]);
                assert(original[perm[bot_si]] == sorted[bot_si]);
                Self::seq_min_le_elem(m2, perm[bot_si]);

                let top_si: int = if bot_si == 0 {
                    if m2[perm[nn-1]] == original[perm[nn-1]] { nn - 1 }
                    else if m2[perm[nn-2]] == original[perm[nn-2]] { nn - 2 }
                    else if m2[perm[nn-3]] == original[perm[nn-3]] { nn - 3 }
                    else {
                        if m2[perm[nn-4]] != original[perm[nn-4]] {
                            Self::num_changes_ge_4(original, m2, perm[nn-4], perm[nn-3], perm[nn-2], perm[nn-1]);
                        }
                        nn - 4
                    }
                } else if bot_si == 1 {
                    if m2[perm[nn-1]] == original[perm[nn-1]] { nn - 1 }
                    else if m2[perm[nn-2]] == original[perm[nn-2]] { nn - 2 }
                    else {
                        if m2[perm[nn-3]] != original[perm[nn-3]] {
                            Self::num_changes_ge_4(original, m2, perm[0], perm[nn-3], perm[nn-2], perm[nn-1]);
                        }
                        nn - 3
                    }
                } else if bot_si == 2 {
                    if m2[perm[nn-1]] == original[perm[nn-1]] { nn - 1 }
                    else {
                        if m2[perm[nn-2]] != original[perm[nn-2]] {
                            Self::num_changes_ge_4(original, m2, perm[0], perm[1], perm[nn-2], perm[nn-1]);
                        }
                        nn - 2
                    }
                } else {
                    if m2[perm[nn-1]] != original[perm[nn-1]] {
                        Self::num_changes_ge_4(original, m2, perm[0], perm[1], perm[2], perm[nn-1]);
                    }
                    nn - 1
                };

                assert(m2[perm[top_si]] == original[perm[top_si]]);
                assert(original[perm[top_si]] == sorted[top_si]);
                Self::seq_max_ge_elem(m2, perm[top_si]);

                assert(top_si >= bot_si + nn - 4);
                assert(sorted[top_si] as int >= sorted[bot_si + nn - 4] as int) by {
                    assert(Self::is_sorted(sorted));
                };
            };
        }
        result
    }
}

}
