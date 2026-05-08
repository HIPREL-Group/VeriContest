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
        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 0;

        while i < n1 && j < n2
            invariant
                n1 == nums1.len(),
                n2 == nums2.len(),
                1 <= n1 <= 100_000,
                1 <= n2 <= 100_000,
                0 <= i <= n1,
                i <= j,
                j <= n2,
                ans < n2,
                forall |k: int| 0 <= k < n1 as int ==> 1 <= #[trigger] nums1[k] <= 100_000,
                forall |k: int| 0 <= k < n2 as int ==> 1 <= #[trigger] nums2[k] <= 100_000,
                forall |a: int, b: int| 0 <= a < b < n1 as int ==> (#[trigger] nums1[a]) >= (#[trigger] nums1[b]),
                forall |a: int, b: int| 0 <= a < b < n2 as int ==> (#[trigger] nums2[a]) >= (#[trigger] nums2[b]),
                ans == 0 || (0 <= best_i < n1 as int && 0 <= best_j < n2 as int && best_i <= best_j && nums1[best_i] <= nums2[best_j] && best_j - best_i == ans as int),
                forall |a: int, b: int| 0 <= a < i as int && 0 <= b < n2 as int && a <= b && a < n1 as int && (#[trigger] nums1[a]) <= (#[trigger] nums2[b]) ==> b - a <= ans as int,
                forall |a: int, b: int| 0 <= a < n1 as int && 0 <= b < j as int && a <= b && (#[trigger] nums1[a]) <= (#[trigger] nums2[b]) ==> b - a <= ans as int,
            decreases n1 - i + n2 - j,
        {
            if nums1[i] <= nums2[j] {
                if j - i > ans {
                    ans = j - i;
                    proof {
                        best_i = i as int;
                        best_j = j as int;
                    }
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
