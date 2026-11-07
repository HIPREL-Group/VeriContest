use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn max_distance(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 100_000,
            1 <= nums2.len() <= 100_000,
            forall |k: int| 0 <= k < nums1.len() ==> 1 <= #[trigger] nums1[k] <= 100_000,
            forall |k: int| 0 <= k < nums2.len() ==> 1 <= #[trigger] nums2[k] <= 100_000,
            forall |a: int, b: int| 0 <= a < b < nums1.len() ==> (#[trigger] nums1[a]) >= (#[trigger] nums1[b]),
            forall |a: int, b: int| 0 <= a < b < nums2.len() ==> (#[trigger] nums2[a]) >= (#[trigger] nums2[b]),
        ensures
            result >= 0,
            forall |a: int, b: int| 0 <= a < nums1.len() && 0 <= b < nums2.len() && a <= b && (#[trigger] nums1[a]) <= (#[trigger] nums2[b]) ==> b - a <= result as int,
            result == 0 || exists |a: int, b: int| 0 <= a < nums1.len() && 0 <= b < nums2.len() && a <= b && (#[trigger] nums1[a]) <= (#[trigger] nums2[b]) && b - a == result as int,
    {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut i: usize = 0;
        let mut j: usize = 0;
        let mut ans: usize = 0;
        while i < n1 && j < n2 {
            if nums1[i] <= nums2[j] {
                if j - i > ans {
                    ans = j - i;
                }
                j = j + 1;
            } else {
                i = i + 1;
                if j < i {
                    j = i;
                }
            }
        }
        ans as i32
    }
}

}
