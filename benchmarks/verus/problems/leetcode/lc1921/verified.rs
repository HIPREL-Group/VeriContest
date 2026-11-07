use vstd::prelude::*;

fn main() {}

verus! {



pub open spec fn is_sorted(s: Seq<i32>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn count_occurrences(s: Seq<i32>, val: i32) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else {
        (if s.last() == val { 1int } else { 0int })
            + count_occurrences(s.drop_last(), val)
    }
}

pub open spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool {
    forall |v: i32| count_occurrences(a, v) == count_occurrences(b, v)
}

proof fn count_occ_nonneg(s: Seq<i32>, val: i32)
    ensures count_occurrences(s, val) >= 0
    decreases s.len()
{
    if s.len() > 0 { count_occ_nonneg(s.drop_last(), val); }
}

proof fn count_occ_append(a: Seq<i32>, b: Seq<i32>, val: i32)
    ensures count_occurrences(a + b, val) == count_occurrences(a, val) + count_occurrences(b, val)
    decreases b.len()
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let ab = a + b;
        assert(ab.drop_last() =~= a + b.drop_last());
        count_occ_append(a, b.drop_last(), val);
    }
}

proof fn perm_refl(s: Seq<i32>)
    ensures is_permutation(s, s)
{}

proof fn perm_trans(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
    requires is_permutation(a, b), is_permutation(b, c)
    ensures is_permutation(a, c)
{}

proof fn perm_append(a1: Seq<i32>, a2: Seq<i32>, b1: Seq<i32>, b2: Seq<i32>)
    requires is_permutation(a1, b1), is_permutation(a2, b2)
    ensures is_permutation(a1 + a2, b1 + b2)
{
    assert forall |v: i32| count_occurrences(a1 + a2, v) == count_occurrences(b1 + b2, v) by {
        count_occ_append(a1, a2, v);
        count_occ_append(b1, b2, v);
    };
}

proof fn count_occ_push(s: Seq<i32>, val: i32, query: i32)
    ensures count_occurrences(s.push(val), query)
        == count_occurrences(s, query) + if val == query { 1int } else { 0int }
{
    assert(s.push(val).drop_last() =~= s);
}



pub open spec fn count_leq(s: Seq<i32>, threshold: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        count_leq(s, threshold, end - 1)
            + if s[end - 1] as int <= threshold { 1int } else { 0int }
    }
}

proof fn count_leq_bounds(s: Seq<i32>, threshold: int, end: int)
    requires 0 <= end <= s.len()
    ensures 0 <= count_leq(s, threshold, end) <= end
    decreases end
{
    if end > 0 { count_leq_bounds(s, threshold, end - 1); }
}

proof fn count_leq_mono(s: Seq<i32>, threshold: int, lo: int, hi: int)
    requires 0 <= lo <= hi, hi <= s.len()
    ensures count_leq(s, threshold, hi) >= count_leq(s, threshold, lo)
    decreases hi - lo
{
    if lo < hi {
        count_leq_mono(s, threshold, lo, hi - 1);
    }
}

proof fn count_leq_suffix_zero(s: Seq<i32>, threshold: int, lo: int, hi: int)
    requires
        lo >= 0, hi <= s.len(), lo <= hi,
        forall |j: int| lo <= j < hi ==> s[j] as int > threshold,
    ensures
        count_leq(s, threshold, hi) == count_leq(s, threshold, lo)
    decreases hi - lo
{
    if lo < hi {
        count_leq_suffix_zero(s, threshold, lo, hi - 1);
    }
}

proof fn count_leq_all_le(s: Seq<i32>, threshold: int, end: int)
    requires
        0 <= end <= s.len(),
        forall |i: int| 0 <= i < end ==> s[i] as int <= threshold,
    ensures
        count_leq(s, threshold, end) == end
    decreases end
{
    if end > 0 {
        count_leq_all_le(s, threshold, end - 1);
    }
}

proof fn count_leq_ext(a: Seq<i32>, b: Seq<i32>, threshold: int, end: int)
    requires
        end >= 0,
        end <= a.len(),
        end <= b.len(),
        forall |k: int| 0 <= k < end ==> a[k] == b[k],
    ensures
        count_leq(a, threshold, end) == count_leq(b, threshold, end)
    decreases end
{
    if end > 0 {
        count_leq_ext(a, b, threshold, end - 1);
    }
}



proof fn sorted_count_leq_upper(s: Seq<i32>, threshold: int, k: int)
    requires
        is_sorted(s),
        0 <= k < s.len(),
        s[k] as int > threshold,
    ensures
        count_leq(s, threshold, s.len() as int) <= k
{
    assert forall |j: int| k <= j < s.len() implies s[j] as int > threshold by {
        assert(s[j] >= s[k]);
    };
    count_leq_suffix_zero(s, threshold, k, s.len() as int);
    count_leq_bounds(s, threshold, k);
}

proof fn sorted_count_leq_lower(s: Seq<i32>, threshold: int, k: int)
    requires
        is_sorted(s),
        0 <= k < s.len(),
        s[k] as int <= threshold,
    ensures
        count_leq(s, threshold, s.len() as int) >= k + 1
{
    assert forall |j: int| 0 <= j <= k implies s[j] as int <= threshold by {
        assert(s[j] <= s[k]);
    };
    count_leq_all_le(s, threshold, k + 1);
    count_leq_mono(s, threshold, k + 1, s.len() as int);
}



proof fn lemma_count_occ_pos_implies_exists(s: Seq<i32>, val: i32)
    requires count_occurrences(s, val) >= 1
    ensures exists |idx: int| 0 <= idx < s.len() && s[idx] == val
    decreases s.len()
{
    if s.len() == 0 { }
    else if s.last() == val {
        assert(s[s.len() - 1] == val);
    } else {
        count_occ_nonneg(s.drop_last(), val);
        lemma_count_occ_pos_implies_exists(s.drop_last(), val);
        let idx = choose |idx: int| 0 <= idx < s.drop_last().len() && s.drop_last()[idx] == val;
        assert(s[idx] == val);
    }
}

proof fn count_occ_remove(s: Seq<i32>, idx: int, val: i32)
    requires 0 <= idx < s.len()
    ensures
        count_occurrences(s, val) ==
            count_occurrences(s.remove(idx), val)
            + if s[idx] == val { 1int } else { 0int }
    decreases s.len()
{
    if idx == s.len() - 1 {
        assert(s.remove(idx) =~= s.drop_last());
    } else {
        assert(s.drop_last().remove(idx) =~= s.remove(idx).drop_last());
        count_occ_remove(s.drop_last(), idx, val);
    }
}

proof fn count_leq_remove_helper(s: Seq<i32>, idx: int, threshold: int, end: int)
    requires 0 <= idx < s.len(), idx < end, end <= s.len()
    ensures
        count_leq(s, threshold, end) ==
            count_leq(s.remove(idx), threshold, end - 1)
            + if s[idx] as int <= threshold { 1int } else { 0int }
    decreases end
{
    if end as int == idx + 1 {
        assert forall |k: int| 0 <= k < idx implies s.remove(idx)[k] == s[k] by {};
        count_leq_ext(s, s.remove(idx), threshold, idx);
    } else {
        count_leq_remove_helper(s, idx, threshold, end - 1);
        assert(s.remove(idx)[end - 2] == s[end - 1]);
    }
}

proof fn perm_preserves_count_leq(a: Seq<i32>, b: Seq<i32>, threshold: int)
    requires
        a.len() == b.len(),
        is_permutation(a, b),
    ensures
        count_leq(a, threshold, a.len() as int) == count_leq(b, threshold, b.len() as int)
    decreases a.len()
{
    if a.len() == 0 { return; }
    let val = a.last();
    count_occ_push(a.drop_last(), val, val);
    assert(a.drop_last().push(val) =~= a);
    count_occ_nonneg(a.drop_last(), val);
    lemma_count_occ_pos_implies_exists(b, val);
    let idx = choose |idx: int| 0 <= idx < b.len() && b[idx] == val;

    let a2 = a.drop_last();
    let b2 = b.remove(idx);
    assert forall |v: i32| count_occurrences(a2, v) == count_occurrences(b2, v) by {
        assert(a.drop_last().push(val) =~= a);
        count_occ_push(a.drop_last(), val, v);
        count_occ_remove(b, idx, v);
    };
    perm_preserves_count_leq(a2, b2, threshold);
    count_leq_ext(a, a2, threshold, (a.len() - 1) as int);
    count_leq_remove_helper(b, idx, threshold, b.len() as int);
    assert(b[idx] == val);
}



pub struct Solution;

impl Solution {
    pub open spec fn arrival_time(d: int, s: int) -> int {
        (d + s - 1) / s
    }

    pub open spec fn count_le(dist: Seq<i32>, speed: Seq<i32>, t: int, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            Self::count_le(dist, speed, t, end - 1)
                + if Self::arrival_time(dist[end - 1] as int, speed[end - 1] as int) <= t {
                    1int
                } else {
                    0int
                }
        }
    }

    proof fn count_le_eq_count_leq(
        dist: Seq<i32>, speed: Seq<i32>, arrivals: Seq<i32>, t: int, end: int,
    )
        requires
            0 <= end <= dist.len(),
            end <= speed.len(),
            end <= arrivals.len(),
            forall |i: int| 0 <= i < end ==>
                arrivals[i] as int == Self::arrival_time(dist[i] as int, speed[i] as int),
        ensures
            Self::count_le(dist, speed, t, end) == count_leq(arrivals, t, end)
        decreases end
    {
        if end > 0 {
            Self::count_le_eq_count_leq(dist, speed, arrivals, t, end - 1);
        }
    }

    proof fn count_le_bounds(dist: Seq<i32>, speed: Seq<i32>, t: int, end: int)
        requires
            0 <= end <= dist.len(),
            end <= speed.len(),
        ensures
            0 <= Self::count_le(dist, speed, t, end) <= end,
        decreases end
    {
        if end > 0 {
            Self::count_le_bounds(dist, speed, t, end - 1);
        }
    }

    fn merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires
            is_sorted(a@),
            is_sorted(b@),
        ensures
            is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            is_permutation(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
            invariant
                0 <= i <= a.len(),
                0 <= j <= b.len(),
                is_sorted(a@),
                is_sorted(b@),
                is_sorted(result@),
                result@.len() == i + j,
                is_permutation(result@, a@.subrange(0, i as int) + b@.subrange(0, j as int)),
                i < a.len() ==> (forall |k: int| 0 <= k < result@.len() ==> result[k] <= a[i as int]),
                j < b.len() ==> (forall |k: int| 0 <= k < result@.len() ==> result[k] <= b[j as int]),
            decreases a.len() - i + b.len() - j,
        {
            let ghost old_result = result@;
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                proof {
                    assert(is_sorted(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q]
                        by {
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
                        count_occurrences(result@, v) == count_occurrences(new_a_prefix + b_prefix, v)
                    by {
                        count_occ_push(old_result, a[i as int], v);
                        count_occ_append(new_a_prefix, b_prefix, v);
                        count_occ_push(old_a_prefix, a[i as int], v);
                        count_occ_append(old_a_prefix, b_prefix, v);
                    };
                }
                i = i + 1;
            } else {
                result.push(b[j]);
                proof {
                    assert(is_sorted(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q]
                        by {
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
                        count_occurrences(result@, v) == count_occurrences(a_prefix + new_b_prefix, v)
                    by {
                        count_occ_push(old_result, b[j as int], v);
                        count_occ_append(a_prefix, new_b_prefix, v);
                        count_occ_push(old_b_prefix, b[j as int], v);
                        count_occ_append(a_prefix, old_b_prefix, v);
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

    fn merge_sort(nums: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            is_sorted(result@),
            result@.len() == nums@.len(),
            is_permutation(result@, nums@),
        decreases nums.len(),
    {
        let n = nums.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(nums[0]);
                proof {
                    assert(result@ =~= nums@);
                    perm_refl(nums@);
                }
            } else {
                proof {
                    assert(result@ =~= nums@);
                    perm_refl(nums@);
                }
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant
                0 <= i <= mid, mid <= n, n == nums.len(),
                left.len() == i,
                forall |k: int| 0 <= k < i as int ==> left[k] == nums[k],
            decreases mid - i,
        {
            left.push(nums[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
            invariant
                mid <= j <= n, n == nums.len(),
                right.len() == j - mid,
                forall |k: int| 0 <= k < (j - mid) as int ==> right[k] == nums[k + mid as int],
            decreases n - j,
        {
            right.push(nums[j]);
            j = j + 1;
        }
        proof {
            assert(left@ =~= nums@.subrange(0, mid as int));
            assert(right@ =~= nums@.subrange(mid as int, n as int));
            assert(nums@ =~= left@ + right@);
            perm_refl(nums@);
        }
        let sorted_left = Self::merge_sort(&left);
        let sorted_right = Self::merge_sort(&right);
        let result = Self::merge(&sorted_left, &sorted_right);
        proof {
            perm_append(sorted_left@, sorted_right@, left@, right@);
            perm_trans(result@, sorted_left@ + sorted_right@, left@ + right@);
            assert(left@ + right@ =~= nums@);
        }
        result
    }

    pub fn eliminate_maximum(dist: Vec<i32>, speed: Vec<i32>) -> (result: i32)
        requires
            dist.len() == speed.len(),
            1 <= dist.len() <= 100_000,
            forall |i: int| 0 <= i < dist.len() ==> 1 <= #[trigger] dist[i] <= 100_000,
            forall |i: int| 0 <= i < speed.len() ==> 1 <= #[trigger] speed[i] <= 100_000,
        ensures
            0 <= result <= dist.len(),
            forall |t: int| 0 <= t < result ==>
                Self::count_le(dist@, speed@, t, dist.len() as int) <= t,
            result < dist.len() as int ==>
                Self::count_le(dist@, speed@, result as int, dist.len() as int) > result as int,
    {
        let n = dist.len();
        let mut arrivals: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == dist.len(),
                n == speed.len(),
                arrivals.len() == i,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] dist[k] <= 100_000,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] speed[k] <= 100_000,
                forall |k: int| 0 <= k < i as int ==>
                    arrivals[k] as int == Self::arrival_time(dist[k] as int, speed[k] as int),
            decreases n - i
        {
            let arrival = (dist[i] + speed[i] - 1) / speed[i];
            proof {
                let ghost d = dist[i as int] as int;
                let ghost s = speed[i as int] as int;
                assert(arrival as int == Self::arrival_time(d, s));
            }
            arrivals.push(arrival);
            i = i + 1;
        }
        let sorted = Self::merge_sort(&arrivals);
        let mut t: usize = 0;
        while t < n
            invariant
                t <= n,
                n == dist.len(),
                n == speed.len(),
                1 <= n <= 100_000,
                sorted.len() == n,
                arrivals.len() == n,
                is_sorted(sorted@),
                is_permutation(sorted@, arrivals@),
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] dist[k] <= 100_000,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] speed[k] <= 100_000,
                forall |k: int| 0 <= k < n as int ==>
                    arrivals[k] as int == Self::arrival_time(dist[k] as int, speed[k] as int),
                forall |t2: int| 0 <= t2 < t as int ==>
                    Self::count_le(dist@, speed@, t2, n as int) <= t2,
            decreases n - t
        {
            if sorted[t] <= t as i32 {
                proof {
                    sorted_count_leq_lower(sorted@, t as int, t as int);
                    perm_preserves_count_leq(sorted@, arrivals@, t as int);
                    Self::count_le_eq_count_leq(dist@, speed@, arrivals@, t as int, n as int);
                }
                return t as i32;
            }
            proof {
                sorted_count_leq_upper(sorted@, t as int, t as int);
                perm_preserves_count_leq(sorted@, arrivals@, t as int);
                Self::count_le_eq_count_leq(dist@, speed@, arrivals@, t as int, n as int);
            }
            t = t + 1;
        }
        proof {
            Self::count_le_bounds(dist@, speed@, 0, n as int);
        }
        n as i32
    }
}

}
