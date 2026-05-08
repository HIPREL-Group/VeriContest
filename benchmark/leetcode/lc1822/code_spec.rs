use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sign_func(x: int) -> int {
    if x > 0 {
        1int
    } else if x < 0 {
        -1int
    } else {
        0int
    }
}

pub open spec fn product_sign(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1int
    } else {
        sign_func(nums[i - 1] as int) * product_sign(nums, i - 1)
    }
}

impl Solution {
    pub fn array_sign(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            res == product_sign(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut sign: i32 = 1;
        let mut i: usize = 0;

        while i < n
        {
            if nums[i] == 0 {
                sign = 0;
            } else if nums[i] < 0 {
                sign = sign * -1;
            }
            i += 1;
        }

        sign
    }
}

} 
