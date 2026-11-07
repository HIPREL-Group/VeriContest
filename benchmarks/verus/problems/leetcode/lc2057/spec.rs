use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
	pub fn smallest_equal(nums: Vec<i32>) -> (result: i32)
		requires
			1 <= nums.len() <= 100,
			forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 9,
		ensures
			result == -1 || 0 <= result < nums.len(),
			result >= 0 ==> nums[result as int] == result as int % 10,
			result >= 0 ==> forall |j: int| 0 <= j < result as int ==> nums[j] != j % 10,
			result == -1 ==> forall |j: int| 0 <= j < nums.len() ==> nums[j] != j % 10,
	{
	}
}

}
