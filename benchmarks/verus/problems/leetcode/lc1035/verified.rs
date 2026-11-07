use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;



pub open spec fn is_strictly_sorted(s: Seq<int>) -> bool {
    forall |k: int, l: int| 0 <= k < l < s.len() ==> s[k] < s[l]
}

pub open spec fn all_in_range(s: Seq<int>, hi: int) -> bool {
    forall |k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s[k] < hi
}

pub open spec fn is_common_subseq(a: Seq<i32>, b: Seq<i32>, ia: Seq<int>, ib: Seq<int>) -> bool {
    ia.len() == ib.len()
    && is_strictly_sorted(ia)
    && is_strictly_sorted(ib)
    && all_in_range(ia, a.len() as int)
    && all_in_range(ib, b.len() as int)
    && (forall |k: int| 0 <= k < ia.len() ==> a[#[trigger] ia[k]] == b[#[trigger] ib[k]])
}



pub open spec fn lcs(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int) -> int
    decreases i, j
{
    if i <= 0 || j <= 0 {
        0
    } else if s1[i - 1] == s2[j - 1] {
        lcs(s1, s2, i - 1, j - 1) + 1
    } else {
        let a = lcs(s1, s2, i - 1, j);
        let b = lcs(s1, s2, i, j - 1);
        if a >= b { a } else { b }
    }
}



pub open spec fn lcs_wit_a(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int) -> Seq<int>
    decreases i, j
{
    if i <= 0 || j <= 0 {
        Seq::empty()
    } else if s1[i - 1] == s2[j - 1] {
        lcs_wit_a(s1, s2, i - 1, j - 1).push(i - 1)
    } else if lcs(s1, s2, i - 1, j) >= lcs(s1, s2, i, j - 1) {
        lcs_wit_a(s1, s2, i - 1, j)
    } else {
        lcs_wit_a(s1, s2, i, j - 1)
    }
}

pub open spec fn lcs_wit_b(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int) -> Seq<int>
    decreases i, j
{
    if i <= 0 || j <= 0 {
        Seq::empty()
    } else if s1[i - 1] == s2[j - 1] {
        lcs_wit_b(s1, s2, i - 1, j - 1).push(j - 1)
    } else if lcs(s1, s2, i - 1, j) >= lcs(s1, s2, i, j - 1) {
        lcs_wit_b(s1, s2, i - 1, j)
    } else {
        lcs_wit_b(s1, s2, i, j - 1)
    }
}



proof fn sorted_push(s: Seq<int>, val: int)
    requires
        is_strictly_sorted(s),
        all_in_range(s, val),
    ensures
        is_strictly_sorted(s.push(val)),
{
    assert forall |k: int, l: int| 0 <= k < l < s.push(val).len()
        implies s.push(val)[k] < s.push(val)[l] by {
        if l < s.len() as int {
        } else {
            assert(s.push(val)[l] == val);
            assert(s.push(val)[k] == s[k]);
        }
    }
}

proof fn in_range_push(s: Seq<int>, val: int, new_hi: int)
    requires
        all_in_range(s, val),
        0 <= val < new_hi,
    ensures
        all_in_range(s.push(val), new_hi),
{
    assert forall |k: int| 0 <= k < s.push(val).len()
        implies 0 <= #[trigger] s.push(val)[k] < new_hi by {
        if k < s.len() as int {
            assert(s.push(val)[k] == s[k]);
        }
    }
}

proof fn in_range_widen(s: Seq<int>, lo: int, hi: int)
    requires
        all_in_range(s, lo),
        lo <= hi,
    ensures
        all_in_range(s, hi),
{
    assert forall |k: int| 0 <= k < s.len()
        implies 0 <= #[trigger] s[k] < hi by {}
}

proof fn sorted_drop_last(s: Seq<int>, hi: int)
    requires
        is_strictly_sorted(s),
        all_in_range(s, hi),
        s.len() > 0,
    ensures
        is_strictly_sorted(s.drop_last()),
        all_in_range(s.drop_last(), s.last()),
{
    let dl = s.drop_last();
    assert forall |k: int, l: int| 0 <= k < l < dl.len()
        implies dl[k] < dl[l] by {
        assert(dl[k] == s[k]);
        assert(dl[l] == s[l]);
    }
    assert forall |k: int| 0 <= k < dl.len()
        implies 0 <= #[trigger] dl[k] < s.last() by {
        assert(dl[k] == s[k]);
        assert(s[k] < s[s.len() - 1]);
    }
}

proof fn matching_drop_last(s1: Seq<i32>, s2: Seq<i32>, ia: Seq<int>, ib: Seq<int>)
    requires
        ia.len() == ib.len(),
        ia.len() > 0,
        forall |k: int| 0 <= k < ia.len() ==> s1[#[trigger] ia[k]] == s2[#[trigger] ib[k]],
    ensures
        forall |k: int| 0 <= k < ia.drop_last().len() ==> s1[#[trigger] ia.drop_last()[k]] == s2[#[trigger] ib.drop_last()[k]],
{
    assert forall |k: int| 0 <= k < ia.drop_last().len()
        implies s1[#[trigger] ia.drop_last()[k]] == s2[#[trigger] ib.drop_last()[k]] by {
        assert(ia.drop_last()[k] == ia[k]);
        assert(ib.drop_last()[k] == ib[k]);
    }
}



proof fn lcs_bounded(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= s1.len(),
        0 <= j <= s2.len(),
    ensures
        0 <= lcs(s1, s2, i, j) <= i,
        0 <= lcs(s1, s2, i, j) <= j,
    decreases i, j
{
    if i <= 0 || j <= 0 {
    } else if s1[i - 1] == s2[j - 1] {
        lcs_bounded(s1, s2, i - 1, j - 1);
    } else {
        lcs_bounded(s1, s2, i - 1, j);
        lcs_bounded(s1, s2, i, j - 1);
    }
}








proof fn lcs_mono_adj(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= s1.len(),
        0 <= j <= s2.len(),
    ensures
        j < s2.len() ==> lcs(s1, s2, i, j) <= lcs(s1, s2, i, j + 1),
        i < s1.len() ==> lcs(s1, s2, i + 1, j) <= lcs(s1, s2, i, j) + 1,
        i < s1.len() ==> lcs(s1, s2, i, j) <= lcs(s1, s2, i + 1, j),
        j < s2.len() ==> lcs(s1, s2, i, j + 1) <= lcs(s1, s2, i, j) + 1,
    decreases i, j
{
    if i == 0 || j == 0 {
        lcs_bounded(s1, s2, i, j);
        if i < s1.len() as int {
            lcs_bounded(s1, s2, i + 1, j);
        }
        if j < s2.len() as int {
            lcs_bounded(s1, s2, i, j + 1);
        }
    } else {
        
        lcs_mono_adj(s1, s2, i - 1, j - 1);

        
        if j >= 2 {
            lcs_mono_adj(s1, s2, i, j - 1);
        } else {
            
            if i < s1.len() as int {
                lcs_bounded(s1, s2, i + 1, 0);
            }
        }

        
        if i >= 2 {
            lcs_mono_adj(s1, s2, i - 1, j);
        } else {
            
            if j < s2.len() as int {
                lcs_bounded(s1, s2, 0, j + 1);
            }
        }

        
        if j < s2.len() as int {
            if s1[i - 1] == s2[j] && s1[i - 1] != s2[j - 1] {
                assert(lcs(s1, s2, i, j - 1) <= lcs(s1, s2, i - 1, j - 1) + 1);
                assert(lcs(s1, s2, i - 1, j - 1) <= lcs(s1, s2, i - 1, j));
                assert(lcs(s1, s2, i, j - 1) <= lcs(s1, s2, i - 1, j) + 1);
            }
        }
        if i < s1.len() as int {
            if s1[i] == s2[j - 1] && s1[i - 1] != s2[j - 1] {
                assert(lcs(s1, s2, i - 1, j) <= lcs(s1, s2, i - 1, j - 1) + 1);
                assert(lcs(s1, s2, i - 1, j - 1) <= lcs(s1, s2, i, j - 1));
                assert(lcs(s1, s2, i - 1, j) <= lcs(s1, s2, i, j - 1) + 1);
            }
        }
    }
}



proof fn lcs_mono(s1: Seq<i32>, s2: Seq<i32>, i1: int, j1: int, i2: int, j2: int)
    requires
        0 <= i1 <= i2 <= s1.len(),
        0 <= j1 <= j2 <= s2.len(),
    ensures
        lcs(s1, s2, i1, j1) <= lcs(s1, s2, i2, j2),
    decreases i2 - i1 + j2 - j1
{
    if i1 == i2 && j1 == j2 {
    } else if j1 < j2 {
        lcs_mono(s1, s2, i1, j1, i2, j2 - 1);
        lcs_mono_adj(s1, s2, i2, j2 - 1);
    } else {
        lcs_mono(s1, s2, i1, j1, i2 - 1, j2);
        lcs_mono_adj(s1, s2, i2 - 1, j2);
    }
}



proof fn lcs_achievable(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= s1.len(),
        0 <= j <= s2.len(),
    ensures
        lcs_wit_a(s1, s2, i, j).len() == lcs_wit_b(s1, s2, i, j).len(),
        is_strictly_sorted(lcs_wit_a(s1, s2, i, j)),
        is_strictly_sorted(lcs_wit_b(s1, s2, i, j)),
        all_in_range(lcs_wit_a(s1, s2, i, j), i),
        all_in_range(lcs_wit_b(s1, s2, i, j), j),
        lcs_wit_a(s1, s2, i, j).len() == lcs(s1, s2, i, j),
        forall |k: int| 0 <= k < lcs_wit_a(s1, s2, i, j).len()
            ==> s1[#[trigger] lcs_wit_a(s1, s2, i, j)[k]] == s2[#[trigger] lcs_wit_b(s1, s2, i, j)[k]],
    decreases i, j
{
    if i <= 0 || j <= 0 {
        assert(lcs_wit_a(s1, s2, i, j) =~= Seq::<int>::empty());
        assert(lcs_wit_b(s1, s2, i, j) =~= Seq::<int>::empty());
    } else if s1[i - 1] == s2[j - 1] {
        lcs_achievable(s1, s2, i - 1, j - 1);
        let prev_a = lcs_wit_a(s1, s2, i - 1, j - 1);
        let prev_b = lcs_wit_b(s1, s2, i - 1, j - 1);
        sorted_push(prev_a, i - 1);
        sorted_push(prev_b, j - 1);
        in_range_push(prev_a, i - 1, i);
        in_range_push(prev_b, j - 1, j);
        assert forall |k: int| 0 <= k < prev_a.push(i - 1).len()
            implies s1[#[trigger] prev_a.push(i - 1)[k]] == s2[#[trigger] prev_b.push(j - 1)[k]] by {
            if k < prev_a.len() as int {
                assert(prev_a.push(i - 1)[k] == prev_a[k]);
                assert(prev_b.push(j - 1)[k] == prev_b[k]);
            } else {
                assert(prev_a.push(i - 1)[k] == i - 1);
                assert(prev_b.push(j - 1)[k] == j - 1);
            }
        }
    } else if lcs(s1, s2, i - 1, j) >= lcs(s1, s2, i, j - 1) {
        lcs_achievable(s1, s2, i - 1, j);
        in_range_widen(lcs_wit_a(s1, s2, i - 1, j), i - 1, i);
    } else {
        lcs_achievable(s1, s2, i, j - 1);
        in_range_widen(lcs_wit_b(s1, s2, i, j - 1), j - 1, j);
    }
}



proof fn lcs_optimal(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int, ia: Seq<int>, ib: Seq<int>)
    requires
        0 <= i <= s1.len(),
        0 <= j <= s2.len(),
        ia.len() == ib.len(),
        is_strictly_sorted(ia),
        is_strictly_sorted(ib),
        all_in_range(ia, i),
        all_in_range(ib, j),
        forall |k: int| 0 <= k < ia.len() ==> s1[#[trigger] ia[k]] == s2[#[trigger] ib[k]],
    ensures
        ia.len() <= lcs(s1, s2, i, j),
    decreases ia.len()
{
    if ia.len() == 0 {
        lcs_bounded(s1, s2, i, j);
    } else {
        let last_a = ia.last();
        let last_b = ib.last();
        sorted_drop_last(ia, i);
        sorted_drop_last(ib, j);
        matching_drop_last(s1, s2, ia, ib);
        lcs_optimal(s1, s2, last_a, last_b, ia.drop_last(), ib.drop_last());
        
        
        assert(s1[last_a] == s2[last_b]);
        assert(lcs(s1, s2, last_a + 1, last_b + 1) == lcs(s1, s2, last_a, last_b) + 1);
        
        lcs_mono(s1, s2, last_a + 1, last_b + 1, i, j);
    }
}

impl Solution {
    pub fn max_uncrossed_lines(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 500,
            1 <= nums2.len() <= 500,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 2000,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 2000,
        ensures
            exists |ia: Seq<int>, ib: Seq<int>| #[trigger] is_common_subseq(nums1@, nums2@, ia, ib) && ia.len() == result as int,
            forall |ia: Seq<int>, ib: Seq<int>| #[trigger] is_common_subseq(nums1@, nums2@, ia, ib) ==> ia.len() <= result as int,
    {
        let m = nums1.len();
        let n = nums2.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n
            invariant
                n <= 500,
                dp.len() == k,
                k <= n + 1,
                forall |c: int| 0 <= c < k as int ==> (#[trigger] dp@[c]) == 0i32,
            decreases (n + 1 - k),
        {
            dp.push(0);
            k = k + 1;
        }

        let mut i: usize = 1;
        while i <= m
            invariant
                m == nums1.len(),
                n == nums2.len(),
                1 <= m <= 500,
                1 <= n <= 500,
                1 <= i <= m + 1,
                dp.len() == n + 1,
                forall |c: int| 0 <= c <= n as int ==>
                    (#[trigger] dp@[c]) as int == lcs(nums1@, nums2@, (i - 1) as int, c),
                forall |idx: int| 0 <= idx < m as int ==> 1 <= #[trigger] nums1@[idx] <= 2000,
                forall |idx: int| 0 <= idx < n as int ==> 1 <= #[trigger] nums2@[idx] <= 2000,
            decreases (m + 1 - i),
        {
            let mut prev: i32 = 0;
            let mut j: usize = 1;
            while j <= n
                invariant
                    m == nums1.len(),
                    n == nums2.len(),
                    1 <= m <= 500,
                    1 <= n <= 500,
                    1 <= i <= m,
                    1 <= j <= n + 1,
                    dp.len() == n + 1,
                    prev as int == lcs(nums1@, nums2@, (i - 1) as int, (j - 1) as int),
                    forall |c: int| 0 <= c < j as int ==>
                        (#[trigger] dp@[c]) as int == lcs(nums1@, nums2@, i as int, c),
                    forall |c: int| j as int <= c <= n as int ==>
                        (#[trigger] dp@[c]) as int == lcs(nums1@, nums2@, (i - 1) as int, c),
                    forall |idx: int| 0 <= idx < m as int ==> 1 <= #[trigger] nums1@[idx] <= 2000,
                    forall |idx: int| 0 <= idx < n as int ==> 1 <= #[trigger] nums2@[idx] <= 2000,
                decreases (n + 1 - j),
            {
                let curr = dp[j];
                proof {
                    lcs_bounded(nums1@, nums2@, (i - 1) as int, (j - 1) as int);
                }

                if nums1[i - 1] == nums2[j - 1] {
                    dp.set(j, prev + 1);
                } else {
                    let a = curr;
                    let b = dp[j - 1];
                    if a >= b {
                        dp.set(j, a);
                    } else {
                        dp.set(j, b);
                    }
                }
                prev = curr;
                j = j + 1;
            }
            i = i + 1;
        }

        proof {
            lcs_bounded(nums1@, nums2@, m as int, n as int);

            
            lcs_achievable(nums1@, nums2@, m as int, n as int);
            let wit_a = lcs_wit_a(nums1@, nums2@, m as int, n as int);
            let wit_b = lcs_wit_b(nums1@, nums2@, m as int, n as int);
            assert(is_common_subseq(nums1@, nums2@, wit_a, wit_b));
            assert(wit_a.len() == dp@[n as int] as int);

            
            assert forall |ia: Seq<int>, ib: Seq<int>|
                #[trigger] is_common_subseq(nums1@, nums2@, ia, ib)
                implies ia.len() <= dp@[n as int] as int by {
                lcs_optimal(nums1@, nums2@, m as int, n as int, ia, ib);
            }
        }

        dp[n]
    }
}

}
