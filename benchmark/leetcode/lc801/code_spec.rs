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
        let n = nums1.len();
        let mut keep: i32 = 0;
        let mut swap: i32 = 1;
        let mut i: usize = 1;
        while i < n {
            let a = nums1[i];
            let b = nums2[i];
            let pa = nums1[i - 1];
            let pb = nums2[i - 1];
            let mut new_keep: i32 = i as i32 + 1;
            let mut new_swap: i32 = i as i32 + 1;
            if a > pa && b > pb {
                if keep < new_keep { new_keep = keep; }
                if swap + 1 < new_swap { new_swap = swap + 1; }
            }
            if a > pb && b > pa {
                if swap < new_keep { new_keep = swap; }
                if keep + 1 < new_swap { new_swap = keep + 1; }
            }
            keep = new_keep;
            swap = new_swap;
            i = i + 1;
        }
        if keep < swap { keep } else { swap }
    }
}

} 
