use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: int) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count(s.drop_last(), v) + if s.last() as int == v { 1nat } else { 0nat }
        }
    }

    pub open spec fn is_shift(nums1: Seq<i32>, nums2: Seq<i32>, x: int) -> bool {
        forall |v: int| Self::count(nums1, v) == #[trigger] Self::count(nums2, v + x)
    }

    pub open spec fn seq_min_prefix(s: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 1 {
            s[0] as int
        } else {
            let m = Self::seq_min_prefix(s, k - 1);
            if (s[k - 1] as int) < m { s[k - 1] as int } else { m }
        }
    }

    pub open spec fn seq_min(s: Seq<i32>) -> int {
        Self::seq_min_prefix(s, s.len() as int)
    }

    proof fn lemma_count_present(s: Seq<i32>, v: int, idx: int)
        requires
            0 <= idx < s.len(),
            s[idx] as int == v,
        ensures
            Self::count(s, v) >= 1,
        decreases s.len()
    {
        if idx < s.len() - 1 {
            Self::lemma_count_present(s.drop_last(), v, idx);
            assert(s.drop_last()[idx] == s[idx]);
        } else {
            assert(s.last() as int == v);
        }
    }

    proof fn lemma_count_pos_present(s: Seq<i32>, v: int)
        requires
            Self::count(s, v) >= 1,
        ensures
            exists |idx: int| 0 <= idx < s.len() && s[idx] as int == v,
        decreases s.len()
    {
        if s.len() == 0 {
            assert(false);
        } else if s.last() as int == v {
            assert(s[s.len() - 1] as int == v);
        } else {
            Self::lemma_count_pos_present(s.drop_last(), v);
            let idx = choose |idx: int| 0 <= idx < s.drop_last().len() && s.drop_last()[idx] as int == v;
            assert(s[idx] == s.drop_last()[idx]);
        }
    }

    pub fn added_integer(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 100,
            nums1.len() == nums2.len(),
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
            exists |x: int| Self::is_shift(nums1@, nums2@, x),
        ensures
            Self::is_shift(nums1@, nums2@, result as int),
            result as int == Self::seq_min(nums2@) - Self::seq_min(nums1@),
    {
        let n = nums1.len();
        let mut min1 = nums1[0];
        let mut min2 = nums2[0];
        let mut i = 1;
        while i < n
            invariant
                n == nums1.len(),
                n == nums2.len(),
                1 <= n <= 100,
                1 <= i <= n,
                0 <= min1 <= 1000,
                0 <= min2 <= 1000,
                forall |j: int| 0 <= j < nums1.len() ==> 0 <= #[trigger] nums1[j] <= 1000,
                forall |j: int| 0 <= j < nums2.len() ==> 0 <= #[trigger] nums2[j] <= 1000,
                exists |j: int| 0 <= j < i && nums1[j] == min1,
                exists |j: int| 0 <= j < i && nums2[j] == min2,
                forall |j: int| 0 <= j < i ==> min1 <= #[trigger] nums1[j],
                forall |j: int| 0 <= j < i ==> min2 <= #[trigger] nums2[j],
                min1 as int == Self::seq_min_prefix(nums1@, i as int),
                min2 as int == Self::seq_min_prefix(nums2@, i as int),
            decreases n - i,
        {
            if nums1[i] < min1 {
                min1 = nums1[i];
            }
            if nums2[i] < min2 {
                min2 = nums2[i];
            }
            i += 1;
        }
        let result = min2 - min1;
        proof {
            let x0 = choose |x: int| Self::is_shift(nums1@, nums2@, x);
            assert(Self::is_shift(nums1@, nums2@, x0));
            assert(forall |v: int| Self::count(nums1@, v) == #[trigger] Self::count(nums2@, v + x0));

            let idx1 = choose |j: int| 0 <= j < n && nums1@[j] == min1;
            Self::lemma_count_present(nums1@, min1 as int, idx1);
            assert(Self::count(nums1@, min1 as int) == Self::count(nums2@, min1 as int + x0));
            assert(Self::count(nums2@, min1 as int + x0) >= 1);
            Self::lemma_count_pos_present(nums2@, min1 as int + x0);
            let idx2 = choose |j: int| 0 <= j < nums2@.len() && nums2@[j] as int == min1 as int + x0;
            assert(min2 <= nums2@[idx2]);
            assert(min2 as int <= min1 as int + x0);

            let jdx2 = choose |j: int| 0 <= j < n && nums2@[j] == min2;
            Self::lemma_count_present(nums2@, min2 as int, jdx2);
            assert(Self::count(nums1@, min2 as int - x0) == Self::count(nums2@, (min2 as int - x0) + x0));
            assert((min2 as int - x0) + x0 == min2 as int);
            assert(Self::count(nums1@, min2 as int - x0) >= 1);
            Self::lemma_count_pos_present(nums1@, min2 as int - x0);
            let jdx1 = choose |j: int| 0 <= j < nums1@.len() && nums1@[j] as int == min2 as int - x0;
            assert(min1 <= nums1@[jdx1]);
            assert(min1 as int <= min2 as int - x0);

            assert(min2 as int == min1 as int + x0);
            assert(result as int == x0);

            assert(Self::is_shift(nums1@, nums2@, result as int)) by {
                assert forall |v: int|
                    Self::count(nums1@, v) == #[trigger] Self::count(nums2@, v + result as int) by {
                    assert(Self::count(nums1@, v) == Self::count(nums2@, v + x0));
                    assert(v + result as int == v + x0);
                }
            }
        }
        min2 - min1
    }
}

}
