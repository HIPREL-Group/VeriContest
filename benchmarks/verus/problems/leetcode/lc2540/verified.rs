use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_common(nums1: Vec<i32>, nums2: Vec<i32>) -> (res: i32)
        requires
            1 <= nums1.len() <= 100_000,
            1 <= nums2.len() <= 100_000,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i < j < nums1.len() ==> nums1[i] <= nums1[j],
            forall |i: int, j: int| 0 <= i < j < nums2.len() ==> nums2[i] <= nums2[j],
        ensures
            res == -1 <==> forall |x: i32| #[trigger] nums1@.contains(x) ==> !nums2@.contains(x),
            res != -1 ==> nums1@.contains(res) && nums2@.contains(res),
            res != -1 ==> forall |x: i32| nums1@.contains(x) && nums2@.contains(x) ==> res <= x,
    {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut i: usize = 0;
        let mut j: usize = 0;

        while i < n1 && j < n2
            invariant
                1 <= nums1.len() <= 100_000,
                1 <= nums2.len() <= 100_000,
                n1 == nums1.len(),
                n2 == nums2.len(),
                0 <= i <= n1,
                0 <= j <= n2,
                forall |k: int| 0 <= k < nums1.len() ==> 1 <= #[trigger] nums1[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < nums2.len() ==> 1 <= #[trigger] nums2[k] <= 1_000_000_000,
                forall |k: int, l: int| 0 <= k < l < nums1.len() ==> nums1[k] <= nums1[l],
                forall |k: int, l: int| 0 <= k < l < nums2.len() ==> nums2[k] <= nums2[l],
                forall |p: int, q: int| 0 <= p < i && 0 <= q < n2 ==> nums1@[p] != nums2@[q],
                forall |p: int, q: int| 0 <= p < n1 && 0 <= q < j ==> nums1@[p] != nums2@[q],
            decreases n1 - i + n2 - j
        {
            if nums1[i] == nums2[j] {
                assert(nums1@.contains(nums1@[i as int]));
                assert(nums2@.contains(nums2@[j as int]));
                assert forall |x: i32| nums1@.contains(x) && nums2@.contains(x) implies nums1@[i as int] <= x by {
                    if nums1@.contains(x) && nums2@.contains(x) {
                        let p = choose |p: int| 0 <= p < n1 && nums1@[p] == x;
                        let q = choose |q: int| 0 <= q < n2 && nums2@[q] == x;
                        if p < (i as int) {
                            assert(nums1@[p] != nums2@[q]);
                            assert(nums1@[p] == nums2@[q]);
                        }
                        if q < (j as int) {
                            assert(nums1@[p] != nums2@[q]);
                            assert(nums1@[p] == nums2@[q]);
                        }
                        assert((i as int) <= p);
                        if (i as int) == p {
                            assert(nums1@[i as int] <= nums1@[p]);
                        } else {
                            assert((i as int) < p);
                            assert(nums1@[i as int] <= nums1@[p]);
                        }
                        assert(nums1@[p] == x);
                    }
                }
                return nums1[i];
            } else if nums1[i] < nums2[j] {
                assert forall |q: int| 0 <= q < n2 implies nums1@[i as int] != nums2@[q] by {
                    if 0 <= q < n2 {
                        if q < (j as int) {
                            assert(nums1@[i as int] != nums2@[q]);
                        } else {
                            assert(nums2@[j as int] <= nums2@[q]);
                            assert(nums1@[i as int] < nums2@[j as int]);
                        }
                    }
                }
                i = i + 1;
            } else {
                assert forall |p: int| 0 <= p < n1 implies nums1@[p] != nums2@[j as int] by {
                    if 0 <= p < n1 {
                        if p < (i as int) {
                            assert(nums1@[p] != nums2@[j as int]);
                        } else {
                            assert(nums1@[i as int] <= nums1@[p]);
                            assert(nums2@[j as int] < nums1@[i as int]);
                        }
                    }
                }
                j = j + 1;
            }
        }

        assert(i == n1 || j == n2);
        assert forall |x: i32| nums1@.contains(x) implies !nums2@.contains(x) by {
            if nums1@.contains(x) {
                if nums2@.contains(x) {
                    let p = choose |p: int| 0 <= p < n1 && nums1@[p] == x;
                    let q = choose |q: int| 0 <= q < n2 && nums2@[q] == x;
                    if i == n1 {
                        assert(p < (i as int));
                        assert(nums1@[p] != nums2@[q]);
                    } else {
                        assert(j == n2);
                        assert(q < (j as int));
                        assert(nums1@[p] != nums2@[q]);
                    }
                    assert(nums1@[p] == nums2@[q]);
                }
            }
        }

        -1
    }
}

}
