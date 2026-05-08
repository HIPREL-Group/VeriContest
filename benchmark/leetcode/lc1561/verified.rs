use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
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

    pub open spec fn even_index_sum(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() < 1 {
            0int
        } else if s.len() < 2 {
            s[0] as int
        } else {
            s[0] as int + Self::even_index_sum(s.subrange(2, s.len() as int))
        }
    }

    proof fn count_occ_nonneg(s: Seq<i32>, val: i32)
        ensures Self::count_occ(s, val) >= 0
        decreases s.len()
    {
        if s.len() > 0 { Self::count_occ_nonneg(s.drop_last(), val); }
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

    proof fn count_occ_elem(s: Seq<i32>, idx: int)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, s[idx]) >= 1
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), s[idx]);
        if idx == s.len() - 1 {
        } else {
            Self::count_occ_elem(s.drop_last(), idx);
            assert(s.drop_last()[idx] == s[idx]);
        }
    }

    proof fn count_occ_positive_means_present(s: Seq<i32>, val: i32)
        requires Self::count_occ(s, val) >= 1
        ensures exists|i: int| 0 <= i < s.len() && s[i] == val
        decreases s.len()
    {
        if s.len() == 0 { return; }
        if s.last() == val { return; }
        Self::count_occ_positive_means_present(s.drop_last(), val);
        let i = choose|i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == val;
        assert(s[i] == val);
    }

    proof fn perm_preserves_bounds(a: Seq<i32>, b: Seq<i32>, lo: int, hi: int)
        requires
            Self::is_perm(a, b),
            forall|i: int| 0 <= i < b.len() ==> lo <= #[trigger] b[i] as int <= hi,
        ensures
            forall|i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] as int <= hi,
    {
        assert forall|i: int| 0 <= i < a.len() implies lo <= #[trigger] a[i] as int <= hi by {
            Self::count_occ_elem(a, i);
            Self::count_occ_positive_means_present(b, a[i]);
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
            let mut result = Vec::new();
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

    proof fn even_index_sum_extend_by_two(s: Seq<i32>, k: int)
        requires
            0 <= k,
            k % 2 == 0,
            k + 2 <= s.len(),
        ensures
            Self::even_index_sum(s.subrange(0, k + 2))
                == s[k] as int + Self::even_index_sum(s.subrange(0, k)),
        decreases k,
    {
        if k == 0 {
            let sub2 = s.subrange(0, 2);
            assert(sub2.len() == 2);
            assert(Self::even_index_sum(sub2)
                == sub2[0] as int + Self::even_index_sum(sub2.subrange(2, 2)));
            assert(sub2.subrange(2, 2).len() == 0);
            assert(Self::even_index_sum(sub2.subrange(2, 2)) == 0);
            assert(Self::even_index_sum(s.subrange(0, 0)) == 0) by {
                assert(s.subrange(0, 0).len() == 0);
            }
            assert(sub2[0] == s[0]) by {
                assert(sub2[0] == s.subrange(0, 2)[0]);
            }
        } else {
            let s2 = s.subrange(2, s.len() as int);
            assert(s.subrange(2, k + 2) =~= s2.subrange(0, k));
            assert(s.subrange(2, k) =~= s2.subrange(0, k - 2));
            Self::even_index_sum_extend_by_two(s2, k - 2);
            let sk2 = s.subrange(0, k + 2);
            assert(Self::even_index_sum(sk2)
                == sk2[0] as int + Self::even_index_sum(sk2.subrange(2, sk2.len() as int)));
            assert(sk2.subrange(2, sk2.len() as int) =~= s.subrange(2, k + 2));
            let sk = s.subrange(0, k);
            assert(Self::even_index_sum(sk)
                == sk[0] as int + Self::even_index_sum(sk.subrange(2, sk.len() as int)));
            assert(sk.subrange(2, sk.len() as int) =~= s.subrange(2, k));
        }
    }

    proof fn even_index_sum_extend_by_one(s: Seq<i32>, k: int)
        requires
            0 <= k,
            k % 2 == 0,
            k + 1 <= s.len(),
        ensures
            Self::even_index_sum(s.subrange(0, k + 1))
                == s[k] as int + Self::even_index_sum(s.subrange(0, k)),
        decreases k,
    {
        if k == 0 {
            let sub1 = s.subrange(0, 1);
            assert(sub1.len() == 1);
            assert(Self::even_index_sum(sub1) == sub1[0] as int);
            assert(Self::even_index_sum(s.subrange(0, 0)) == 0) by {
                assert(s.subrange(0, 0).len() == 0);
            }
            assert(sub1[0] == s[0]);
        } else {
            let s2 = s.subrange(2, s.len() as int);
            assert(s.subrange(2, k + 1) =~= s2.subrange(0, k - 1));
            assert(s.subrange(2, k) =~= s2.subrange(0, k - 2));
            Self::even_index_sum_extend_by_one(s2, k - 2);
            let sk1 = s.subrange(0, k + 1);
            assert(Self::even_index_sum(sk1)
                == sk1[0] as int + Self::even_index_sum(sk1.subrange(2, sk1.len() as int)));
            assert(sk1.subrange(2, sk1.len() as int) =~= s.subrange(2, k + 1));
            let sk = s.subrange(0, k);
            assert(Self::even_index_sum(sk)
                == sk[0] as int + Self::even_index_sum(sk.subrange(2, sk.len() as int)));
            assert(sk.subrange(2, sk.len() as int) =~= s.subrange(2, k));
        }
    }

    pub fn max_coins(piles: Vec<i32>) -> (result: i32)
        requires
            3 <= piles.len() <= 100000,
            piles.len() % 3 == 0,
            forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
        ensures
            exists|sorted_piles: Seq<i32>|
                Self::sorted(sorted_piles)
                && sorted_piles.len() == piles.len()
                && result as int == Self::even_index_sum(
                    sorted_piles.subrange(
                        (sorted_piles.len() / 3) as int,
                        sorted_piles.len() as int,
                    ),
                ),
    {
        let sorted = Self::ms_sort(&piles);
        let n = sorted.len();

        proof {
            Self::perm_preserves_bounds(sorted@, piles@, 1, 10000);
        }

        let mut sum: i32 = 0;
        let third = n / 3;
        let mut k = third;
        let ghost tail = sorted@.subrange(third as int, n as int);
        let ghost tail_len = tail.len();

        while k < n
            invariant
                third <= k <= n,
                n == sorted.len(),
                n <= 100000,
                n % 3 == 0,
                third == n / 3,
                (k - third) % 2 == 0,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] sorted[j] <= 10000,
                Self::sorted(sorted@),
                tail == sorted@.subrange(third as int, n as int),
                tail_len == n - third,
                sum as int == Self::even_index_sum(tail.subrange(0, (k - third) as int)),
                0 <= sum <= ((k - third) / 2) as int * 10000,
            decreases n - k,
        {
            let ghost idx = (k - third) as int;
            proof {
                assert(tail[idx] == sorted@[k as int]) by {
                    assert(sorted@.subrange(third as int, n as int)[idx] == sorted@[third as int + idx]);
                }
                if (k + 1) < n {
                    Self::even_index_sum_extend_by_two(tail, idx);
                } else {
                    Self::even_index_sum_extend_by_one(tail, idx);
                }
            }
            sum = sum + sorted[k];
            k = k + 2;
        }

        proof {
            assert(tail.subrange(0, tail_len as int) =~= tail);
        }

        sum
    }
}

}
