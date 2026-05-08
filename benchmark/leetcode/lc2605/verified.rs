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
        let mut min1: i32 = 10;
        let mut common_min: i32 = 10;
        let mut i: usize = 0;
        while i < nums1.len()
            invariant
                1 <= nums1.len() <= 9,
                1 <= nums2.len() <= 9,
                forall |p: int| 0 <= p < nums1.len() ==> 1 <= #[trigger] nums1[p] <= 9,
                forall |p: int| 0 <= p < nums2.len() ==> 1 <= #[trigger] nums2[p] <= 9,
                forall |p: int, q: int| 0 <= p < q < nums1.len() ==> nums1[p] != nums1[q],
                forall |p: int, q: int| 0 <= p < q < nums2.len() ==> nums2[p] != nums2[q],
                0 <= i <= nums1.len(),
                min1 as int == Self::min_digit_upto(nums1@, i as int),
                common_min as int == Self::min_common_upto(nums1@, nums2@, i as int),
                1 <= min1 <= 10,
                1 <= common_min <= 10,
            decreases nums1.len() - i,
        {
            let d = nums1[i];
            if d < min1 {
                min1 = d;
            }
            let mut found = false;
            let mut j: usize = 0;
            while j < nums2.len()
                invariant
                    1 <= nums2.len() <= 9,
                    forall |p: int| 0 <= p < nums2.len() ==> 1 <= #[trigger] nums2[p] <= 9,
                    0 <= j <= nums2.len(),
                    found == Self::contains_upto(nums2@, d as int, j as int),
                decreases nums2.len() - j,
            {
                if nums2[j] == d {
                    found = true;
                }
                j = j + 1;
            }
            if found && d < common_min {
                common_min = d;
            }
            i = i + 1;
        }

        if common_min < 10 {
            return common_min;
        }

        let mut min2: i32 = 10;
        let mut k: usize = 0;
        while k < nums2.len()
            invariant
                1 <= nums2.len() <= 9,
                forall |p: int| 0 <= p < nums2.len() ==> 1 <= #[trigger] nums2[p] <= 9,
                0 <= k <= nums2.len(),
                min2 as int == Self::min_digit_upto(nums2@, k as int),
                1 <= min2 <= 10,
            decreases nums2.len() - k,
        {
            if nums2[k] < min2 {
                min2 = nums2[k];
            }
            k = k + 1;
        }

        if min1 < min2 {
            min1 * 10 + min2
        } else {
            min2 * 10 + min1
        }
    }
}

}
