use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn popcount_helper(x: int, acc: int) -> int
        decreases x,
    {
        if x <= 0 {
            acc
        } else {
            Self::popcount_helper(x / 2, acc + (x % 2))
        }
    }

    pub open spec fn popcount(x: int) -> int {
        Self::popcount_helper(x, 0)
    }

    pub open spec fn scan_spec(
        nums: Seq<i32>,
        i: int,
        has_prev: bool,
        prev_max: int,
        curr_bits: int,
        curr_min: int,
        curr_max: int,
    ) -> bool
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            !has_prev || prev_max <= curr_min
        } else {
            let x = nums[i] as int;
            let b = Self::popcount(x);
            if b == curr_bits {
                Self::scan_spec(
                    nums,
                    i + 1,
                    has_prev,
                    prev_max,
                    curr_bits,
                    Self::min_int(curr_min, x),
                    Self::max_int(curr_max, x),
                )
            } else {
                (!has_prev || prev_max <= curr_min)
                && Self::scan_spec(nums, i + 1, true, curr_max, b, x, x)
            }
        }
    }

    pub open spec fn can_sort_array_spec(nums: Seq<i32>) -> bool {
        if nums.len() == 0 {
            true
        } else {
            let x0 = nums[0] as int;
            Self::scan_spec(nums, 1, false, 0, Self::popcount(x0), x0, x0)
        }
    }

    pub fn can_sort_array(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 256,
        ensures
            result <==> Self::can_sort_array_spec(nums@),
    {
    }
}

}
