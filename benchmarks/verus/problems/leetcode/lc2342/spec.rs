use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum_spec(x: nat) -> nat
        decreases x,
    {
        if x == 0 {
            0
        } else {
            (x % 10) + Self::digit_sum_spec(x / 10)
        }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, i: int, j: int) -> bool {
        0 <= i < j < nums.len()
            && Self::digit_sum_spec(nums[i] as nat) == Self::digit_sum_spec(nums[j] as nat)
    }

    pub fn maximum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            -1 <= result as int <= 2000000000,
            result == -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() ==> !(#[trigger] Self::valid_pair(nums@, i, j)),
            result != -1 ==> exists |i: int, j: int|
                0 <= i < j < nums.len()
                && Self::valid_pair(nums@, i, j)
                && result as int == nums[i] as int + nums[j] as int,
            result != -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() && #[trigger] Self::valid_pair(nums@, i, j)
                ==> nums[i] as int + nums[j] as int <= result as int,
    {
    }
}

}
