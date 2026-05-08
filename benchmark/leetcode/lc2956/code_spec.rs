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
            decreases nums1.len() - i,
        {
            let cur = nums1[i];
            let mut ok = false;
            let mut j: usize = 0;
            while j < nums2.len()
                decreases nums2.len() - j,
            {
                if cur == nums2[j] {
                    ok = true;
                    break;
                }
                j = j + 1;
            }
            if ok {
                c1 = c1 + 1;
            }
            i = i + 1;
        }

        let mut c2: usize = 0;
        i = 0;
        while i < nums2.len()
            decreases nums2.len() - i,
        {
            let cur = nums2[i];
            let mut ok = false;
            let mut j: usize = 0;
            while j < nums1.len()
                decreases nums1.len() - j,
            {
                if cur == nums1[j] {
                    ok = true;
                    break;
                }
                j = j + 1;
            }
            if ok {
                c2 = c2 + 1;
            }
            i = i + 1;
        }

        let mut out: Vec<i32> = Vec::new();
        out.push(c1 as i32);
        out.push(c2 as i32);
        out
    }
}

}
