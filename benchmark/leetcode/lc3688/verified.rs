use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn even_or_prefix(nums: Seq<i32>, k: int) -> i32
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            let prev = Self::even_or_prefix(nums, k - 1);
            if nums[k - 1] % 2 == 0 {
                prev | nums[k - 1]
            } else {
                prev
            }
        }
    }

    pub fn even_number_bitwise_o_rs(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == Self::even_or_prefix(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                0 <= i <= n,
                result == Self::even_or_prefix(nums@, i as int),
            decreases n - i,
        {
            let ghost old_i = i as int;
            let old_result = result;

            if nums[i] % 2 == 0 {
                result = result | nums[i];
            }

            proof {
                assert(0 <= old_i < nums.len());
                if nums[old_i] % 2 == 0 {
                    assert(Self::even_or_prefix(nums@, old_i + 1) == Self::even_or_prefix(nums@, old_i) | nums[old_i]);
                    assert(result == old_result | nums[old_i]);
                } else {
                    assert(Self::even_or_prefix(nums@, old_i + 1) == Self::even_or_prefix(nums@, old_i));
                    assert(result == old_result);
                }
                assert(result == Self::even_or_prefix(nums@, old_i + 1));
            }

            i = i + 1;
        }
        result
    }
}

}
