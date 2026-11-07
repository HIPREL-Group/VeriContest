use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_ops_from(nums: Seq<i32>, i: int, flip: int) -> int
        decreases if i < nums.len() { nums.len() - i } else { 0 },
    {
        if i < nums.len() {
            if nums[i] as int == flip {
                1 + Self::min_ops_from(nums, i + 1, 1 - flip)
            } else {
                Self::min_ops_from(nums, i + 1, flip)
            }
        } else {
            0
        }
    }

    pub open spec fn min_operations_spec(nums: Seq<i32>, result: int) -> bool {
        &&& 1 <= nums.len() <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1)
        &&& result == Self::min_ops_from(nums, 0, 0)
    }

    pub fn min_operations(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
        ensures
            Self::min_operations_spec(nums@, result as int),
    {
        let n = nums.len();
        let mut ans = 0i32;
        let mut flip = 0i32;
        let mut i = 0usize;
        while i < n
            invariant
                1 <= n <= 100000,
                n == nums.len(),
                0 <= i <= n,
                0 <= ans <= i as int,
                flip == 0 || flip == 1,
                ans as int + Self::min_ops_from(nums@, i as int, flip as int) == Self::min_ops_from(nums@, 0, 0),
            decreases n - i,
        {
            assert(i < n);
            if nums[i] == flip {
                assert(Self::min_ops_from(nums@, i as int, flip as int) == 1 + Self::min_ops_from(nums@, i as int + 1, 1 - (flip as int)));
                ans = ans + 1;
                flip = if flip == 0 { 1 } else { 0 };
            } else {
                assert(Self::min_ops_from(nums@, i as int, flip as int) == Self::min_ops_from(nums@, i as int + 1, flip as int));
            }
            i += 1;
        }
        assert(Self::min_ops_from(nums@, n as int, flip as int) == 0);
        assert(ans as int == Self::min_ops_from(nums@, 0, 0));
        ans
    }
}

}
