use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_upto(s: Seq<i32>, d: int, upto: int) -> bool
        decreases if upto <= 0 { 0int } else { upto }
    {
        if upto <= 0 {
            false
        } else {
            Self::contains_upto(s, d, upto - 1) || s[(upto - 1) as int] as int == d
        }
    }

    pub open spec fn min_digit_upto(s: Seq<i32>, upto: int) -> int
        decreases if upto <= 0 { 0int } else { upto }
    {
        if upto <= 0 {
            10
        } else {
            let prev = Self::min_digit_upto(s, upto - 1);
            let x = s[(upto - 1) as int] as int;
            if x < prev { x } else { prev }
        }
    }

    pub open spec fn min_common_upto(nums1: Seq<i32>, nums2: Seq<i32>, upto: int) -> int
        decreases if upto <= 0 { 0int } else { upto }
    {
        if upto <= 0 {
            10
        } else {
            let prev = Self::min_common_upto(nums1, nums2, upto - 1);
            let x = nums1[(upto - 1) as int] as int;
            if Self::contains_upto(nums2, x, nums2.len() as int) && x < prev { x } else { prev }
        }
    }

    pub open spec fn answer_spec(nums1: Seq<i32>, nums2: Seq<i32>) -> int {
        let c = Self::min_common_upto(nums1, nums2, nums1.len() as int);
        if c < 10 {
            c
        } else {
            let a = Self::min_digit_upto(nums1, nums1.len() as int);
            let b = Self::min_digit_upto(nums2, nums2.len() as int);
            if a < b { a * 10 + b } else { b * 10 + a }
        }
    }

    pub fn min_number(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 9,
            1 <= nums2.len() <= 9,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 9,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 9,
            forall |i: int, j: int| 0 <= i < j < nums1.len() ==> nums1[i] != nums1[j],
            forall |i: int, j: int| 0 <= i < j < nums2.len() ==> nums2[i] != nums2[j],
        ensures
            result as int == Self::answer_spec(nums1@, nums2@),
    {
    }
}

}
