use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rob_spec(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
        decreases i,
    {
        if i <= 0 {
            nums[0] as int
        } else if i == 1 {
            if nums[0] as int > nums[1] as int { nums[0] as int } else { nums[1] as int }
        } else {
            let skip = Self::rob_spec(nums, i - 1);
            let take = Self::rob_spec(nums, i - 2) + nums[i] as int;
            if take > skip { take } else { skip }
        }
    }

    proof fn rob_bounds(nums: Seq<i32>, i: int)
        requires
            1 <= nums.len() <= 100,
            forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 400 as i32,
            0 <= i < nums.len(),
        ensures
            0 <= Self::rob_spec(nums, i) <= 400 * (i + 1),
        decreases i,
    {
        if i >= 2 {
            Self::rob_bounds(nums, i - 1);
            Self::rob_bounds(nums, i - 2);
        }
    }

    pub fn rob(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 400,
        ensures
            result == Self::rob_spec(nums@, (nums.len() - 1) as int),
    {
        let n = nums.len();
        if n == 1 {
            return nums[0];
        }
        let mut a = nums[0];
        let mut b = if nums[0] > nums[1] { nums[0] } else { nums[1] };
        let mut i: usize = 2;

        proof {
            Self::rob_bounds(nums@, 0);
            Self::rob_bounds(nums@, 1);
        }

        while i < n
            invariant
                2 <= i <= n,
                n == nums.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] nums@[j] <= 400,
                a as int == Self::rob_spec(nums@, (i - 2) as int),
                b as int == Self::rob_spec(nums@, (i - 1) as int),
                0 <= a <= 40000,
                0 <= b <= 40000,
            decreases n - i,
        {
            proof {
                Self::rob_bounds(nums@, i as int);
                Self::rob_bounds(nums@, (i - 1) as int);
                Self::rob_bounds(nums@, (i - 2) as int);
            }
            let c = if a + nums[i] > b { a + nums[i] } else { b };
            a = b;
            b = c;
            i = i + 1;
        }

        b
    }
}

} 
