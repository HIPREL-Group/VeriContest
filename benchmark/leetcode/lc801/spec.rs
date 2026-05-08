use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn keep_spec(nums1: Seq<i32>, nums2: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums1.len(),
            nums1.len() == nums2.len(),
        decreases i,
    {
        if i <= 0 {
            0int
        } else {
            let pa = nums1[i - 1] as int;
            let pb = nums2[i - 1] as int;
            let a = nums1[i] as int;
            let b = nums2[i] as int;
            let prev_keep = Self::keep_spec(nums1, nums2, i - 1);
            let prev_swap = Self::swap_spec(nums1, nums2, i - 1);
            let from_keep = if a > pa && b > pb { prev_keep } else { i + 1 };
            let from_swap = if a > pb && b > pa { prev_swap } else { i + 1 };
            if from_keep <= from_swap { from_keep } else { from_swap }
        }
    }

    pub open spec fn swap_spec(nums1: Seq<i32>, nums2: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums1.len(),
            nums1.len() == nums2.len(),
        decreases i,
    {
        if i <= 0 {
            1int
        } else {
            let pa = nums1[i - 1] as int;
            let pb = nums2[i - 1] as int;
            let a = nums1[i] as int;
            let b = nums2[i] as int;
            let prev_keep = Self::keep_spec(nums1, nums2, i - 1);
            let prev_swap = Self::swap_spec(nums1, nums2, i - 1);
            let from_keep = if a > pb && b > pa { prev_keep + 1 } else { i + 1 };
            let from_swap = if a > pa && b > pb { prev_swap + 1 } else { i + 1 };
            if from_keep <= from_swap { from_keep } else { from_swap }
        }
    }

    pub fn min_swap(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            2 <= nums1.len() <= 100_000,
            nums1.len() == nums2.len(),
            forall|i: int| 0 <= i < nums1.len() ==>
                0 <= #[trigger] nums1[i],
            forall|i: int| 0 <= i < nums2.len() ==>
                0 <= #[trigger] nums2[i],
        ensures
            result >= 0,
            result as int == {
                let n = nums1@.len();
                let k = Self::keep_spec(nums1@, nums2@, (n - 1) as int);
                let s = Self::swap_spec(nums1@, nums2@, (n - 1) as int);
                if k <= s { k } else { s }
            },
    {
    }
}

} 
