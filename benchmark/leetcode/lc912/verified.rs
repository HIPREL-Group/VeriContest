use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
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
        a.len() == b.len() && forall|v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    proof fn count_occ_append(a: Seq<i32>, b: Seq<i32>, val: i32)
        ensures Self::count_occ(a + b, val) == Self::count_occ(a, val) + Self::count_occ(b, val)
        decreases b.len()
    {
        if b.len() == 0 {
            assert(a + b =~= a);
        } else {
            assert((a + b).drop_last() =~= a + b.drop_last());
            Self::count_occ_append(a, b.drop_last(), val);
        }
    }

    proof fn count_occ_push(s: Seq<i32>, val: i32, query: i32)
        ensures Self::count_occ(s.push(val), query)
            == Self::count_occ(s, query) + if val == query { 1int } else { 0int }
    {
        assert(s.push(val).drop_last() =~= s);
    }

    proof fn perm_append(a1: Seq<i32>, a2: Seq<i32>, b1: Seq<i32>, b2: Seq<i32>)
        requires Self::is_perm(a1, b1), Self::is_perm(a2, b2)
        ensures Self::is_perm(a1 + a2, b1 + b2)
    {
        assert forall|v: i32|
            Self::count_occ(a1 + a2, v) == Self::count_occ(b1 + b2, v)
        by {
            Self::count_occ_append(a1, a2, v);
            Self::count_occ_append(b1, b2, v);
        };
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::sorted(a@), Self::sorted(b@)
        ensures
            Self::sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
            invariant
                0 <= i <= a.len(), 0 <= j <= b.len(),
                Self::sorted(a@), Self::sorted(b@),
                Self::sorted(result@),
                result@.len() == i + j,
                Self::is_perm(result@, a@.subrange(0, i as int) + b@.subrange(0, j as int)),
                i < a.len() ==> (forall|k: int| 0 <= k < result@.len() ==> result[k] <= a[i as int]),
                j < b.len() ==> (forall|k: int| 0 <= k < result@.len() ==> result[k] <= b[j as int]),
            decreases a.len() - i + b.len() - j,
        {
            let ghost old_result = result@;
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                proof {
                    assert(Self::sorted(result@)) by {
                        assert forall|p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q]
                        by {
                            if q < old_result.len() as int { }
                            else if p < old_result.len() as int { assert(result[q] == a[i as int]); }
                        };
                    };
                    let new_ap = a@.subrange(0, (i + 1) as int);
                    let old_ap = a@.subrange(0, i as int);
                    let bp = b@.subrange(0, j as int);
                    assert(new_ap =~= old_ap.push(a[i as int]));
                    assert(result@ =~= old_result.push(a[i as int]));
                    assert forall|v: i32|
                        Self::count_occ(result@, v) == Self::count_occ(new_ap + bp, v)
                    by {
                        Self::count_occ_push(old_result, a[i as int], v);
                        Self::count_occ_append(new_ap, bp, v);
                        Self::count_occ_push(old_ap, a[i as int], v);
                        Self::count_occ_append(old_ap, bp, v);
                    };
                }
                i = i + 1;
            } else {
                result.push(b[j]);
                proof {
                    assert(Self::sorted(result@)) by {
                        assert forall|p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q]
                        by {
                            if q < old_result.len() as int { }
                            else if p < old_result.len() as int { assert(result[q] == b[j as int]); }
                        };
                    };
                    let ap = a@.subrange(0, i as int);
                    let new_bp = b@.subrange(0, (j + 1) as int);
                    let old_bp = b@.subrange(0, j as int);
                    assert(new_bp =~= old_bp.push(b[j as int]));
                    assert(result@ =~= old_result.push(b[j as int]));
                    assert forall|v: i32|
                        Self::count_occ(result@, v) == Self::count_occ(ap + new_bp, v)
                    by {
                        Self::count_occ_push(old_result, b[j as int], v);
                        Self::count_occ_append(ap, new_bp, v);
                        Self::count_occ_push(old_bp, b[j as int], v);
                        Self::count_occ_append(ap, old_bp, v);
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

    fn ms_sort(nums: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::sorted(result@),
            Self::is_perm(result@, nums@),
        decreases nums.len(),
    {
        let n = nums.len();
        if n <= 1 {
            let mut result: Vec<i32> = Vec::new();
            if n == 1 {
                result.push(nums[0]);
                proof { assert(result@ =~= nums@); }
            } else {
                proof { assert(result@ =~= nums@); }
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
                forall|k: int| 0 <= k < i as int ==> left[k] == nums[k],
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
                forall|k: int| 0 <= k < (j - mid) as int ==> right[k] == nums[k + mid as int],
            decreases n - j,
        {
            right.push(nums[j]);
            j = j + 1;
        }

        proof {
            assert(left@ =~= nums@.subrange(0, mid as int));
            assert(right@ =~= nums@.subrange(mid as int, n as int));
            assert(nums@ =~= left@ + right@);
        }

        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);

        proof {
            Self::perm_append(sorted_left@, sorted_right@, left@, right@);
            assert forall|v: i32|
                Self::count_occ(result@, v) == Self::count_occ(nums@, v)
            by {
                assert(Self::count_occ(result@, v)
                    == Self::count_occ(sorted_left@ + sorted_right@, v));
                assert(Self::count_occ(sorted_left@ + sorted_right@, v)
                    == Self::count_occ(left@ + right@, v));
                assert(left@ + right@ =~= nums@);
            };
        }

        result
    }

    pub fn sort_array(nums: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= nums.len() <= 50_000,
            forall|i: int| 0 <= i < nums.len() ==> -50_000 <= #[trigger] nums[i] <= 50_000,
        ensures
            Self::sorted(res@),
            Self::is_perm(res@, nums@),
    {
        Self::ms_sort(&nums)
    }
}

}
