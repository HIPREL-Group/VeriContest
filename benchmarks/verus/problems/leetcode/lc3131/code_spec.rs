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
        while i < n {
            if nums1[i] < min1 {
                min1 = nums1[i];
            }
            if nums2[i] < min2 {
                min2 = nums2[i];
            }
            i += 1;
        }
        min2 - min1
    }
}

}
