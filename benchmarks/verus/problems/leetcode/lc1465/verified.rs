use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
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

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn max_adj_diff(sorted: Seq<i32>, bound: int) -> int
        decreases sorted.len(),
    {
        if sorted.len() == 0 {
            bound
        } else {
            Self::spec_max(
                bound - sorted[sorted.len() - 1] as int,
                Self::max_adj_diff(sorted.drop_last(), sorted[sorted.len() - 1] as int)
            )
        }
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
            assert((a + b).drop_last() =~= a + b.drop_last());
            Self::count_occ_append(a, b.drop_last(), val);
        }
    }

    proof fn count_occ_elem(s: Seq<i32>, idx: int)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, s[idx]) >= 1
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), s[idx]);
        if idx < s.len() - 1 {
            Self::count_occ_elem(s.drop_last(), idx);
            assert(s.drop_last()[idx] == s[idx]);
        }
    }

    proof fn count_occ_positive_means_present(s: Seq<i32>, val: i32)
        requires Self::count_occ(s, val) >= 1
        ensures exists |i: int| 0 <= i < s.len() && s[i] == val
        decreases s.len()
    {
        if s.len() == 0 { return; }
        if s.last() == val { return; }
        Self::count_occ_positive_means_present(s.drop_last(), val);
        let i = choose |i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == val;
        assert(s[i] == val);
    }

    proof fn count_occ_zero_if_absent(s: Seq<i32>, val: i32)
        requires forall |i: int| 0 <= i < s.len() ==> s[i] != val
        ensures Self::count_occ(s, val) == 0
        decreases s.len()
    {
        if s.len() == 0 { return; }
        assert forall |i: int| 0 <= i < s.drop_last().len()
            implies s.drop_last()[i] != val by { assert(s[i] != val); };
        Self::count_occ_zero_if_absent(s.drop_last(), val);
    }

    proof fn count_occ_two(s: Seq<i32>, i: int, j: int)
        requires 0 <= i < j < s.len(), s[i] == s[j]
        ensures Self::count_occ(s, s[i]) >= 2
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), s[i]);
        if j == s.len() - 1 {
            Self::count_occ_elem(s.drop_last(), i);
        } else {
            Self::count_occ_two(s.drop_last(), i, j);
        }
    }

    proof fn count_occ_distinct_le_1(s: Seq<i32>, val: i32)
        requires forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
        ensures Self::count_occ(s, val) <= 1
        decreases s.len()
    {
        if s.len() <= 1 { return; }
        Self::count_occ_nonneg(s.drop_last(), val);
        if s.last() == val {
            Self::count_occ_zero_if_absent(s.drop_last(), val);
        } else {
            assert forall |i: int, j: int| 0 <= i < j < s.drop_last().len()
                implies s.drop_last()[i] != s.drop_last()[j] by { assert(s[i] != s[j]); };
            Self::count_occ_distinct_le_1(s.drop_last(), val);
        }
    }

    proof fn perm_preserves_bounds(a: Seq<i32>, b: Seq<i32>, lo: int, hi: int)
        requires
            Self::is_perm(a, b),
            forall |i: int| 0 <= i < b.len() ==> lo <= #[trigger] b[i] as int <= hi,
        ensures
            forall |i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] as int <= hi,
    {
        assert forall |i: int| 0 <= i < a.len()
            implies lo <= #[trigger] a[i] as int <= hi by {
            Self::count_occ_elem(a, i);
            Self::count_occ_positive_means_present(b, a[i]);
        };
    }

    proof fn perm_preserves_distinct(a: Seq<i32>, b: Seq<i32>)
        requires
            Self::is_perm(a, b),
            forall |i: int, j: int| 0 <= i < j < b.len() ==> b[i] != b[j],
        ensures
            forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] != a[j],
    {
        assert forall |i: int, j: int| 0 <= i < j < a.len()
            implies a[i] != a[j] by {
            if a[i] == a[j] {
                Self::count_occ_two(a, i, j);
                Self::count_occ_distinct_le_1(b, a[i]);
            }
        };
    }

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
            Self::is_perm(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
                proof { assert(result@ =~= input@); }
            } else {
                proof { assert(result@ =~= input@); }
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
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        proof {
            Self::perm_append(sorted_left@, sorted_right@, left@, right@);
            assert forall |v: i32|
                Self::count_occ(result@, v) == Self::count_occ(input@, v)
            by {
                assert(Self::count_occ(result@, v)
                    == Self::count_occ(sorted_left@ + sorted_right@, v));
                assert(Self::count_occ(sorted_left@ + sorted_right@, v)
                    == Self::count_occ(left@ + right@, v));
                assert(left@ + right@ =~= input@);
            };
        }
        result
    }

    

    fn find_max_gap(cuts: &Vec<i32>, bound: i32) -> (result: i32)
        requires
            1 <= cuts.len() <= 100_000,
            bound >= 2,
            forall |k: int| 0 <= k < cuts.len() ==> 1 <= #[trigger] cuts[k] < bound,
            forall |k: int, m: int| 0 <= k < m < cuts.len() ==> cuts[k] != cuts[m],
        ensures
            1 <= result < bound,
            exists |sorted: Seq<i32>|
                Self::is_sorted(sorted)
                && Self::is_perm(sorted, cuts@)
                && result as int == Self::max_adj_diff(sorted, bound as int),
    {
        let sorted = Self::ms_sort(cuts);
        let n = sorted.len();

        proof {
            Self::perm_preserves_bounds(sorted@, cuts@, 1, bound as int - 1);
            Self::perm_preserves_distinct(sorted@, cuts@);
        }

        let mut max_g: i32 = sorted[0];
        let mut i: usize = 1;

        
        
        while i < n
            invariant
                1 <= i <= n,
                n == sorted.len(),
                n == cuts.len(),
                n >= 1,
                bound >= 2,
                Self::is_sorted(sorted@),
                Self::is_perm(sorted@, cuts@),
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] sorted[k] < bound,
                forall |k: int, j: int| 0 <= k < j < n as int ==> sorted[k] != sorted[j],
                max_g as int == Self::max_adj_diff(
                    sorted@.subrange(0, (i - 1) as int), sorted[i as int - 1] as int),
                1 <= max_g,
                max_g < bound,
            decreases n - i,
        {
            let gap = sorted[i] - sorted[i - 1];
            proof {
                assert(sorted[i as int] > sorted[i as int - 1]) by {
                    assert(sorted[i as int] != sorted[i as int - 1]);
                    assert(sorted[i as int] >= sorted[i as int - 1]);
                };
                
                
                
                
                
                let sub = sorted@.subrange(0, i as int);
                assert(sub.drop_last() =~= sorted@.subrange(0, (i - 1) as int));
                assert(sub[sub.len() - 1] == sorted[i as int - 1]);
            }
            if gap > max_g {
                max_g = gap;
            }
            i = i + 1;
        }

        
        
        
        
        let last_gap = bound - sorted[n - 1];
        if last_gap > max_g {
            max_g = last_gap;
        }

        proof {
            assert(sorted@.drop_last() =~= sorted@.subrange(0, (n - 1) as int));
        }

        max_g
    }

    pub fn max_area(h: i32, w: i32, horizontal_cuts: Vec<i32>, vertical_cuts: Vec<i32>) -> (result: i32)
        requires
            2 <= h <= 1_000_000_000,
            2 <= w <= 1_000_000_000,
            1 <= horizontal_cuts.len() <= 100_000,
            1 <= vertical_cuts.len() <= 100_000,
            forall |i: int| 0 <= i < horizontal_cuts.len() ==> 1 <= #[trigger] horizontal_cuts[i] < h,
            forall |j: int| 0 <= j < vertical_cuts.len() ==> 1 <= #[trigger] vertical_cuts[j] < w,
            forall |i: int, j: int| 0 <= i < j < horizontal_cuts.len() ==> horizontal_cuts[i] != horizontal_cuts[j],
            forall |i: int, j: int| 0 <= i < j < vertical_cuts.len() ==> vertical_cuts[i] != vertical_cuts[j],
        ensures
            0 <= result < 1_000_000_007,
            exists |sh: Seq<i32>, sv: Seq<i32>|
                Self::is_sorted(sh)
                && Self::is_perm(sh, horizontal_cuts@)
                && Self::is_sorted(sv)
                && Self::is_perm(sv, vertical_cuts@)
                && result as int == (Self::max_adj_diff(sh, h as int) * Self::max_adj_diff(sv, w as int)) % 1_000_000_007,
    {
        let max_h = Self::find_max_gap(&horizontal_cuts, h);
        let max_v = Self::find_max_gap(&vertical_cuts, w);
        proof {
            assert((max_h as int) * (max_v as int) < 1_000_000_000 * 1_000_000_000) by(nonlinear_arith)
                requires
                    max_h >= 1,
                    max_h < 1_000_000_000,
                    max_v >= 1,
                    max_v < 1_000_000_000,
            ;
            let sh = choose |s: Seq<i32>| Self::is_sorted(s) && Self::is_perm(s, horizontal_cuts@)
                && max_h as int == Self::max_adj_diff(s, h as int);
            let sv = choose |s: Seq<i32>| Self::is_sorted(s) && Self::is_perm(s, vertical_cuts@)
                && max_v as int == Self::max_adj_diff(s, w as int);
            assert(Self::is_sorted(sh) && Self::is_perm(sh, horizontal_cuts@)
                && Self::is_sorted(sv) && Self::is_perm(sv, vertical_cuts@)
                && (max_h as int * max_v as int) % 1_000_000_007
                   == (Self::max_adj_diff(sh, h as int) * Self::max_adj_diff(sv, w as int)) % 1_000_000_007
            );
        }
        ((max_h as i64 * max_v as i64) % 1_000_000_007i64) as i32
    }
}

}
