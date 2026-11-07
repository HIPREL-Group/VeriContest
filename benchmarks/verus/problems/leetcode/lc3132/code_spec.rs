use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_plain_prefix(nums: Seq<i32>, end: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0int
        } else {
            Self::count_plain_prefix(nums, end - 1, v) + if nums[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn count_shift_prefix(nums: Seq<i32>, end: int, x: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0int
        } else {
            Self::count_shift_prefix(nums, end - 1, x, v) + if nums[end - 1] as int + x == v { 1int } else { 0int }
        }
    }

    pub open spec fn valid_x_spec(nums1: Seq<i32>, nums2: Seq<i32>, x: int) -> bool {
        forall |v: int| 0 <= v <= 1000 ==> Self::count_shift_prefix(nums1, nums1.len() as int, x, v) >= Self::count_plain_prefix(nums2, nums2.len() as int, v)
    }

    pub fn minimum_added_integer(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            3 <= nums1.len() <= 200,
            nums2.len() + 2 == nums1.len(),
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
            exists |x: int| -1000 <= x <= 1000 && Self::valid_x_spec(nums1@, nums2@, x),
        ensures
            -1000 <= result <= 1000,
            Self::valid_x_spec(nums1@, nums2@, result as int),
            forall |x: int| -1000 <= x < result ==> !Self::valid_x_spec(nums1@, nums2@, x),
    {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut x = -1000;
        while x <= 1000 {
            let mut ok = true;
            let mut v = 0;
            let mut fail_v = -1;
            while v <= 1000 && ok {
                let mut c1 = 0;
                let mut i: usize = 0;
                while i < n1 {
                    if nums1[i] as i64 + x as i64 == v as i64 {
                        c1 += 1;
                    }
                    i += 1;
                }
                let mut c2 = 0;
                let mut j: usize = 0;
                while j < n2 {
                    if nums2[j] as i64 == v as i64 {
                        c2 += 1;
                    }
                    j += 1;
                }
                if c1 < c2 {
                    ok = false;
                    fail_v = v;
                }
                v += 1;
            }
            if ok {
                return x;
            }
            let _ = fail_v;
            x += 1;
        }
        0
    }
}

}
