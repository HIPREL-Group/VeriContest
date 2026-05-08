use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_spec(nums: Seq<i32>, target: int) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] as int == target
    }

    pub open spec fn in_two_of_three(v: int, nums1: Seq<i32>, nums2: Seq<i32>, nums3: Seq<i32>) -> bool {
        let in1 = Self::contains_spec(nums1, v);
        let in2 = Self::contains_spec(nums2, v);
        let in3 = Self::contains_spec(nums3, v);
        (in1 && in2) || (in1 && in3) || (in2 && in3)
    }

    pub open spec fn collect_upto(nums1: Seq<i32>, nums2: Seq<i32>, nums3: Seq<i32>, limit: int) -> Seq<i32>
        decreases limit,
    {
        if limit <= 0 {
            seq![]
        } else {
            let prev = Self::collect_upto(nums1, nums2, nums3, limit - 1);
            if Self::in_two_of_three(limit, nums1, nums2, nums3) {
                prev.push(limit as i32)
            } else {
                prev
            }
        }
    }

    fn contains_num(nums: &Vec<i32>, target: i32) -> (found: bool)
        ensures
            found == Self::contains_spec(nums@, target as int),
    {
        let n = nums.len();
        let mut i: usize = 0;
        let mut found = false;
        while i < n {
            if nums[i] == target {
                found = true;
            }
            i += 1;
        }
        found
    }

    pub fn two_out_of_three(nums1: Vec<i32>, nums2: Vec<i32>, nums3: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums1.len() <= 100,
            1 <= nums2.len() <= 100,
            1 <= nums3.len() <= 100,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 100,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 100,
            forall |i: int| 0 <= i < nums3.len() ==> 1 <= #[trigger] nums3[i] <= 100,
        ensures
            result@ == Self::collect_upto(nums1@, nums2@, nums3@, 100),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut v: i32 = 1;
        while v <= 100 {
            let in1 = Self::contains_num(&nums1, v);
            let in2 = Self::contains_num(&nums2, v);
            let in3 = Self::contains_num(&nums3, v);
            let good = (in1 && in2) || (in1 && in3) || (in2 && in3);
            if good {
                result.push(v);
            }
            v += 1;
        }
        result
    }
}

}
