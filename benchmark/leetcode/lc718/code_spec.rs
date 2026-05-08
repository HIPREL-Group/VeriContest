use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn common_at(a: Seq<i32>, b: Seq<i32>, i: int, j: int, L: int) -> bool {
        0 <= i && i + L <= a.len()
        && 0 <= j && j + L <= b.len()
        && forall |k: int| 0 <= k < L ==> (#[trigger] a[i + k]) == b[j + k]
    }

    pub fn find_length(nums1: Vec<i32>, nums2: Vec<i32>) -> (res: i32)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            (nums1.len() + 1) * (nums2.len() + 1) <= usize::MAX,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 100,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 100,
        ensures
            res >= 0,
            res <= (nums1.len() as int) && res <= (nums2.len() as int),
            exists |i: int, j: int| Self::common_at(nums1@, nums2@, i, j, res as int),
            forall |L: int, i: int, j: int|
                (L > res as int && (#[trigger] Self::common_at(nums1@, nums2@, i, j, L))) ==> false,
    {
        let m = nums1.len();
        let n = nums2.len();
        let total = (m + 1) * (n + 1);
        let mut dp: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        while idx < total
        {
            dp.push(0);
            idx += 1;
        }
        let mut max_len = 0i32;
        let mut i = 1usize;
        while i <= m
        {
            let mut j = 1usize;
            while j <= n
            {
                let cur_idx = i * (n + 1) + j;
                let prev_idx = (i - 1) * (n + 1) + (j - 1);
                if nums1[i - 1] == nums2[j - 1] {
                    let val = dp[prev_idx] + 1;
                    dp.set(cur_idx, val);
                    if val > max_len {
                        max_len = val;
                    }
                } else {
                    dp.set(cur_idx, 0);
                }
                j += 1;
            }
            i += 1;
        }
        max_len
    }
}

}
