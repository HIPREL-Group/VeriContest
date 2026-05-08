use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted_seq(s: Seq<i32>) -> bool {
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
        forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn is_ap(s: Seq<i32>) -> bool {
        s.len() <= 1 || forall |i: int| 0 <= i < s.len() - 1 ==>
            s[i + 1] as int - (#[trigger] s[i]) as int == s[1] as int - s[0] as int
    }

    pub open spec fn can_form_ap(s: Seq<i32>) -> bool {
        exists |sorted: Seq<i32>|
            sorted.len() == s.len() &&
            Self::is_sorted_seq(sorted) &&
            Self::is_perm(s, sorted) &&
            Self::is_ap(sorted)
    }

    proof fn count_occ_nonneg(s: Seq<i32>, val: i32)
        ensures Self::count_occ(s, val) >= 0
        decreases s.len()
    {
        if s.len() > 0 { Self::count_occ_nonneg(s.drop_last(), val); }
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
        assert forall |v: i32|
            Self::count_occ(a1 + a2, v) == Self::count_occ(b1 + b2, v) by {
            Self::count_occ_append(a1, a2, v);
            Self::count_occ_append(b1, b2, v);
        };
    }

    proof fn count_occ_elem(s: Seq<i32>, idx: int)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, s[idx]) >= 1
        decreases s.len()
    {
        if idx == s.len() - 1 {
            Self::count_occ_nonneg(s.drop_last(), s[idx]);
        } else {
            Self::count_occ_elem(s.drop_last(), idx);
            assert(s.drop_last()[idx] == s[idx]);
        }
    }

    proof fn count_occ_positive_means_present(s: Seq<i32>, val: i32)
        requires Self::count_occ(s, val) >= 1
        ensures exists |i: int| 0 <= i < s.len() && s[i] == val
        decreases s.len()
    {
        if s.last() == val {
            assert(s[s.len() - 1] == val);
        } else {
            Self::count_occ_positive_means_present(s.drop_last(), val);
            let i = choose |i: int|
                0 <= i < s.drop_last().len() && s.drop_last()[i] == val;
            assert(s[i] == s.drop_last()[i]);
        }
    }

    proof fn perm_preserves_bounds(a: Seq<i32>, b: Seq<i32>, lo: i32, hi: i32)
        requires
            Self::is_perm(a, b),
            forall |i: int| 0 <= i < a.len()
                ==> lo <= #[trigger] a[i] && a[i] <= hi,
        ensures
            forall |i: int| 0 <= i < b.len()
                ==> lo <= #[trigger] b[i] && b[i] <= hi,
    {
        assert forall |i: int| 0 <= i < b.len()
            implies lo <= #[trigger] b[i] && b[i] <= hi by {
            Self::count_occ_elem(b, i);
            Self::count_occ_positive_means_present(a, b[i]);
        };
    }

    proof fn sorted_perm_unique(a: Seq<i32>, b: Seq<i32>)
        requires
            a.len() == b.len(),
            Self::is_sorted_seq(a),
            Self::is_sorted_seq(b),
            Self::is_perm(a, b),
        ensures
            a =~= b,
        decreases a.len(),
    {
        if a.len() > 0 {
            
            Self::count_occ_elem(a, 0);
            Self::count_occ_positive_means_present(b, a[0]);
            let kb = choose |i: int| 0 <= i < b.len() && b[i] == a[0];
            assert(b[0] <= b[kb]);
            
            Self::count_occ_elem(b, 0);
            Self::count_occ_positive_means_present(a, b[0]);
            let ka = choose |i: int| 0 <= i < a.len() && a[i] == b[0];
            assert(a[0] <= a[ka]);
            
            assert(a[0] == b[0]);

            let a_head: Seq<i32> = Seq::new(1, |_i: int| a[0]);
            let b_head: Seq<i32> = Seq::new(1, |_i: int| b[0]);
            let a_tail = a.subrange(1, a.len() as int);
            let b_tail = b.subrange(1, b.len() as int);
            assert(a =~= a_head + a_tail);
            assert(b =~= b_head + b_tail);
            assert(a_head =~= b_head);

            assert forall |v: i32|
                Self::count_occ(a_tail, v) == Self::count_occ(b_tail, v) by {
                Self::count_occ_append(a_head, a_tail, v);
                Self::count_occ_append(b_head, b_tail, v);
            };

            assert(Self::is_sorted_seq(a_tail)) by {
                assert forall |i: int, j: int|
                    0 <= i <= j < a_tail.len()
                    implies a_tail[i] <= a_tail[j] by {
                    assert(a_tail[i] == a[i + 1]);
                    assert(a_tail[j] == a[j + 1]);
                };
            };
            assert(Self::is_sorted_seq(b_tail)) by {
                assert forall |i: int, j: int|
                    0 <= i <= j < b_tail.len()
                    implies b_tail[i] <= b_tail[j] by {
                    assert(b_tail[i] == b[i + 1]);
                    assert(b_tail[j] == b[j + 1]);
                };
            };

            Self::sorted_perm_unique(a_tail, b_tail);

            assert forall |i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                if i > 0 {
                    assert(a[i] == a_tail[i - 1]);
                    assert(b[i] == b_tail[i - 1]);
                }
            };
        }
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires
            Self::is_sorted_seq(a@),
            Self::is_sorted_seq(b@),
        ensures
            Self::is_sorted_seq(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
            invariant
                0 <= i <= a.len(),
                0 <= j <= b.len(),
                Self::is_sorted_seq(a@),
                Self::is_sorted_seq(b@),
                Self::is_sorted_seq(result@),
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
                    assert(Self::is_sorted_seq(result@)) by {
                        assert forall |p: int, q: int|
                            0 <= p <= q < result@.len()
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
                            == Self::count_occ(new_a_prefix + b_prefix, v)
                    by {
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
                    assert(Self::is_sorted_seq(result@)) by {
                        assert forall |p: int, q: int|
                            0 <= p <= q < result@.len()
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
                            == Self::count_occ(a_prefix + new_b_prefix, v)
                    by {
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

    fn ms_sort(nums: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted_seq(result@),
            result@.len() == nums@.len(),
            Self::is_perm(result@, nums@),
        decreases nums.len(),
    {
        let n = nums.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(nums[0]);
                proof {
                    assert(result@ =~= nums@);
                }
            } else {
                proof {
                    assert(result@ =~= nums@);
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
                forall |k: int| 0 <= k < (j - mid) as int
                    ==> right[k] == nums[k + mid as int],
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
            assert(left@ + right@ =~= nums@);
        }
        result
    }

    pub fn can_make_arithmetic_progression(arr: Vec<i32>) -> (res: bool)
        requires
            2 <= arr.len() <= 1000,
            forall |i: int| 0 <= i < arr.len() ==>
                -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
        ensures
            res == Self::can_form_ap(arr@),
    {
        let sorted = Self::ms_sort(&arr);
        let n = sorted.len();
        proof {
            Self::perm_preserves_bounds(arr@, sorted@,
                -1_000_000i32, 1_000_000i32);
        }
        if n <= 1 {
            proof {
                assert(Self::is_ap(sorted@));
            }
            return true;
        }
        let d = sorted[1] - sorted[0];
        let mut i: usize = 2;
        while i < n
            invariant
                2 <= i <= n,
                n == sorted.len(),
                n == arr.len(),
                n >= 2,
                d == sorted[1] - sorted[0],
                Self::is_sorted_seq(sorted@),
                Self::is_perm(sorted@, arr@),
                forall |k: int| 0 <= k < n as int ==>
                    -1_000_000 <= #[trigger] sorted[k] <= 1_000_000,
                forall |k: int| 0 <= k < i as int - 1 ==>
                    sorted[k + 1] as int - (#[trigger] sorted[k]) as int == d as int,
            decreases n - i,
        {
            if sorted[i] - sorted[i - 1] != d {
                proof {
                    assert(sorted[i as int] as int - sorted[(i - 1) as int] as int
                        != sorted[1] as int - sorted[0] as int);
                    assert(!Self::is_ap(sorted@));
                    assert forall |s: Seq<i32>|
                        s.len() == arr@.len()
                        && Self::is_sorted_seq(s)
                        && Self::is_perm(arr@, s)
                        && Self::is_ap(s)
                    implies false by {
                        Self::sorted_perm_unique(sorted@, s);
                        assert(s =~= sorted@);
                    };
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            assert(Self::is_ap(sorted@)) by {
                assert forall |k: int| 0 <= k < sorted@.len() - 1
                    implies sorted@[k + 1] as int - (#[trigger] sorted@[k]) as int
                        == sorted@[1] as int - sorted@[0] as int by {
                };
            };
        }
        true
    }
}

}
