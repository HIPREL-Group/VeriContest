use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_between(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        decreases hi - lo,
    {
        if lo >= hi { 0 }
        else { (if s[lo] == v { 1int } else { 0int }) + Self::count_between(s, v, lo + 1, hi) }
    }

    pub fn merge(nums1: &mut Vec<i32>, m: i32, nums2: &mut Vec<i32>, n: i32)
        requires
            0 <= m,
            0 <= n,
            1 <= m + n <= 200,
            old(nums1).len() == (m + n) as int,
            old(nums2).len() == n as int,
            forall |i: int| 0 <= i < m as int ==>
                -1_000_000_000 <= #[trigger] old(nums1)[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < n as int ==>
                -1_000_000_000 <= #[trigger] old(nums2)[i] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i <= j < m as int ==>
                old(nums1)[i] <= old(nums1)[j],
            forall |i: int, j: int| 0 <= i <= j < n as int ==>
                old(nums2)[i] <= old(nums2)[j],
        ensures
            nums1.len() == old(nums1).len(),
            nums2.len() == old(nums2).len(),
            forall |i: int, j: int| 0 <= i <= j < nums1.len() ==>
                nums1[i] <= nums1[j],
            forall |v: i32| Self::count_between(nums1@, v, 0, nums1.len() as int) ==
                Self::count_between(old(nums1)@, v, 0, m as int) +
                Self::count_between(old(nums2)@, v, 0, n as int),
    {
        let mm = m as usize;
        let nn = n as usize;
        let total = mm + nn;
        let mut i: usize = mm;
        let mut j: usize = nn;

        while i > 0 || j > 0 {
            let w: usize = i + j - 1;

            if j == 0 || (i > 0 && nums1[i - 1] >= nums2[j - 1]) {
                i = i - 1;
                let v = nums1[i];
                nums1.set(w, v);
            } else {
                j = j - 1;
                let v = nums2[j];
                nums1.set(w, v);
            }
        }
    }
}

}
