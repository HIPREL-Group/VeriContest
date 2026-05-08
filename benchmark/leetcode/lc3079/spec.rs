use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn max3(a: int, b: int, c: int) -> int {
        Self::max2(Self::max2(a, b), c)
    }

    pub open spec fn max4(a: int, b: int, c: int, d: int) -> int {
        Self::max2(Self::max3(a, b, c), d)
    }

    pub open spec fn encrypt_int(x: int) -> int {
        if x < 10 {
            x
        } else if x < 100 {
            let d0 = x % 10;
            let d1 = x / 10;
            11 * Self::max2(d0, d1)
        } else if x < 1000 {
            let d0 = x % 10;
            let d1 = (x / 10) % 10;
            let d2 = x / 100;
            111 * Self::max3(d0, d1, d2)
        } else {
            let d0 = x % 10;
            let d1 = (x / 10) % 10;
            let d2 = (x / 100) % 10;
            let d3 = x / 1000;
            1111 * Self::max4(d0, d1, d2, d3)
        }
    }

    pub open spec fn sum_encrypted(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_encrypted(nums, end - 1) + Self::encrypt_int(nums[end - 1] as int)
        }
    }

    pub fn sum_of_encrypted_int(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::sum_encrypted(nums@, nums.len() as int),
    {
    }
}

}
