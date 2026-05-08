use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn added_integer(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 100,
            nums1.len() == nums2.len(),
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> #[trigger] nums1[i] as int + (nums2[0] as int - nums1[0] as int) == nums2[i] as int,
        ensures
            forall |i: int| 0 <= i < nums1.len() ==> #[trigger] nums1[i] as int + result as int == nums2[i] as int,
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
                forall |j: int| 0 <= j < nums1.len() ==> #[trigger] nums1[j] as int + (nums2[0] as int - nums1[0] as int) == nums2[j] as int,
                exists |j: int| 0 <= j < i && nums1[j] == min1,
                exists |j: int| 0 <= j < i && nums2[j] == min2,
                forall |j: int| 0 <= j < i ==> min1 <= #[trigger] nums1[j],
                forall |j: int| 0 <= j < i ==> min2 <= #[trigger] nums2[j],
            decreases n - i,
        {
            if nums1[i] < min1 {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies nums1[i as int] <= #[trigger] nums1[j] by {
                        if j < i as int {
                            assert(min1 <= nums1[j]);
                            assert(nums1[i as int] < min1);
                        } else {
                            assert(j == i as int);
                        }
                    }
                }
                min1 = nums1[i];
            } else {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies min1 <= #[trigger] nums1[j] by {
                        if j < i as int {
                            assert(min1 <= nums1[j]);
                        } else {
                            assert(j == i as int);
                            assert(min1 <= nums1[i as int]);
                        }
                    }
                }
            }
            if nums2[i] < min2 {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies nums2[i as int] <= #[trigger] nums2[j] by {
                        if j < i as int {
                            assert(min2 <= nums2[j]);
                            assert(nums2[i as int] < min2);
                        } else {
                            assert(j == i as int);
                        }
                    }
                }
                min2 = nums2[i];
            } else {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies min2 <= #[trigger] nums2[j] by {
                        if j < i as int {
                            assert(min2 <= nums2[j]);
                        } else {
                            assert(j == i as int);
                            assert(min2 <= nums2[i as int]);
                        }
                    }
                }
            }
            i += 1;
        }
        let result = min2 - min1;
        proof {
            let shift = nums2[0] as int - nums1[0] as int;
            let idx1 = choose |j: int| 0 <= j < nums1.len() && nums1[j] == min1;
            let idx2 = choose |j: int| 0 <= j < nums2.len() && nums2[j] == min2;
            assert(0 <= idx1 < nums1.len());
            assert(0 <= idx2 < nums2.len());
            assert(nums1[idx1] == min1);
            assert(nums2[idx2] == min2);
            assert(nums1[idx1] as int + shift == nums2[idx1] as int);
            assert(nums1[idx2] as int + shift == nums2[idx2] as int);
            assert(min2 <= nums2[idx1]);
            assert(min1 <= nums1[idx2]);
            assert(min2 as int <= min1 as int + shift);
            assert(min1 as int + shift <= min2 as int);
            assert(result as int == min2 as int - min1 as int);
            assert(result as int == shift);
            assert forall |j: int| 0 <= j < nums1.len() implies #[trigger] nums1[j] as int + result as int == nums2[j] as int by {
                assert(nums1[j] as int + shift == nums2[j] as int);
            }
        }
        min2 - min1
    }
}

}
