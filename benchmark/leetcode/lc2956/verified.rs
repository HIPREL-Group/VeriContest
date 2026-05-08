use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_seq(s: Seq<i32>, x: i32) -> bool {
        exists |j: int| 0 <= j < s.len() && s[j] == x
    }

    pub open spec fn count_in_other_prefix(a: Seq<i32>, b: Seq<i32>, n: nat) -> nat
        recommends
            n <= a.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::count_in_other_prefix(a, b, (n - 1) as nat)
                + if Self::in_seq(b, a[(n - 1) as int]) { 1nat } else { 0nat }
        }
    }

    pub fn find_intersection_values(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
        requires
            nums1.len() <= 2147483647usize,
            nums2.len() <= 2147483647usize,
        ensures
            result.len() == 2,
            result[0] as nat == Self::count_in_other_prefix(nums1@, nums2@, nums1.len() as nat),
            result[1] as nat == Self::count_in_other_prefix(nums2@, nums1@, nums2.len() as nat),
            0 <= result[0] <= nums1.len() as i32,
            0 <= result[1] <= nums2.len() as i32,
    {
        let mut c1: usize = 0;
        let mut i: usize = 0;
        while i < nums1.len()
            invariant
                0 <= i <= nums1.len(),
                0 <= c1 <= i,
                c1 as nat == Self::count_in_other_prefix(nums1@, nums2@, i as nat),
            decreases nums1.len() - i,
        {
            let cur = nums1[i];
            let mut ok = false;
            let mut j: usize = 0;
            while j < nums2.len()
                invariant
                    0 <= j <= nums2.len(),
                    i < nums1.len(),
                    cur == nums1[i as int],
                decreases nums2.len() - j,
            {
                if cur == nums2[j] {
                    ok = true;
                    break;
                }
                j = j + 1;
            }

            assert(cur == nums1[i as int]);
            let mut real_ok = false;
            j = 0;
            while j < nums2.len()
                invariant
                    0 <= j <= nums2.len(),
                    i < nums1.len(),
                    cur == nums1[i as int],
                    real_ok <==> exists |t: int| 0 <= t < j && nums2[t] == cur,
                decreases nums2.len() - j,
            {
                if cur == nums2[j] {
                    real_ok = true;
                }
                j = j + 1;
            }
            assert(real_ok <==> Self::in_seq(nums2@, cur));

            let ghost old_c1 = c1;
            if ok {
                c1 = c1 + 1;
            }
            if real_ok {
                if !ok {
                    c1 = c1 + 1;
                }
            } else {
                if ok {
                    c1 = c1 - 1;
                }
            }
            assert(Self::count_in_other_prefix(nums1@, nums2@, (i + 1) as nat)
                == Self::count_in_other_prefix(nums1@, nums2@, i as nat)
                    + if Self::in_seq(nums2@, nums1[i as int]) { 1nat } else { 0nat });
            if real_ok {
                assert(Self::in_seq(nums2@, nums1[i as int]));
                if ok {
                    assert(c1 == old_c1 + 1);
                } else {
                    assert(c1 == old_c1 + 1);
                }
                assert(c1 as nat == old_c1 as nat + 1nat);
            } else {
                assert(!Self::in_seq(nums2@, nums1[i as int]));
                if ok {
                    assert(c1 == old_c1);
                } else {
                    assert(c1 == old_c1);
                }
                assert(c1 as nat == old_c1 as nat + 0nat);
            }
            i = i + 1;
        }

        let mut c2: usize = 0;
        i = 0;
        while i < nums2.len()
            invariant
                0 <= i <= nums2.len(),
                0 <= c2 <= i,
                c2 as nat == Self::count_in_other_prefix(nums2@, nums1@, i as nat),
            decreases nums2.len() - i,
        {
            let cur = nums2[i];
            let mut ok = false;
            let mut j: usize = 0;
            while j < nums1.len()
                invariant
                    0 <= j <= nums1.len(),
                    i < nums2.len(),
                    cur == nums2[i as int],
                decreases nums1.len() - j,
            {
                if cur == nums1[j] {
                    ok = true;
                    break;
                }
                j = j + 1;
            }

            assert(cur == nums2[i as int]);
            let mut real_ok = false;
            j = 0;
            while j < nums1.len()
                invariant
                    0 <= j <= nums1.len(),
                    i < nums2.len(),
                    cur == nums2[i as int],
                    real_ok <==> exists |t: int| 0 <= t < j && nums1[t] == cur,
                decreases nums1.len() - j,
            {
                if cur == nums1[j] {
                    real_ok = true;
                }
                j = j + 1;
            }
            assert(real_ok <==> Self::in_seq(nums1@, cur));

            let ghost old_c2 = c2;
            if ok {
                c2 = c2 + 1;
            }
            if real_ok {
                if !ok {
                    c2 = c2 + 1;
                }
            } else {
                if ok {
                    c2 = c2 - 1;
                }
            }
            assert(Self::count_in_other_prefix(nums2@, nums1@, (i + 1) as nat)
                == Self::count_in_other_prefix(nums2@, nums1@, i as nat)
                    + if Self::in_seq(nums1@, nums2[i as int]) { 1nat } else { 0nat });
            if real_ok {
                assert(Self::in_seq(nums1@, nums2[i as int]));
                if ok {
                    assert(c2 == old_c2 + 1);
                } else {
                    assert(c2 == old_c2 + 1);
                }
                assert(c2 as nat == old_c2 as nat + 1nat);
            } else {
                assert(!Self::in_seq(nums1@, nums2[i as int]));
                if ok {
                    assert(c2 == old_c2);
                } else {
                    assert(c2 == old_c2);
                }
                assert(c2 as nat == old_c2 as nat + 0nat);
            }
            i = i + 1;
        }

        let mut out: Vec<i32> = Vec::new();
        assert(c1 <= nums1.len());
        assert(c2 <= nums2.len());
        out.push(c1 as i32);
        out.push(c2 as i32);
        assert(out.len() == 2);
        out
    }
}

}
