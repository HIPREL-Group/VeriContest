use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rob_spec(nums: Seq<i32>, lo: int, hi: int) -> int
        recommends
            0 <= lo <= hi < nums.len(),
        decreases hi - lo,
    {
        if hi < lo {
            0
        } else if hi == lo {
            nums[lo] as int
        } else if hi == lo + 1 {
            if nums[lo] as int > nums[hi] as int { nums[lo] as int } else { nums[hi] as int }
        } else {
            let skip = Self::rob_spec(nums, lo, hi - 1);
            let take = Self::rob_spec(nums, lo, hi - 2) + nums[hi] as int;
            if take > skip { take } else { skip }
        }
    }

    proof fn rob_bounds(nums: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo <= hi < nums.len(),
            forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1000,
        ensures
            0 <= Self::rob_spec(nums, lo, hi) <= 1000 * (hi - lo + 1),
        decreases hi - lo,
    {
        if hi > lo + 1 {
            Self::rob_bounds(nums, lo, hi - 1);
            Self::rob_bounds(nums, lo, hi - 2);
        }
    }

    pub fn rob(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result == if nums@.len() == 1 {
                nums@[0] as int
            } else {
                let n = nums@.len() as int;
                let r1 = Self::rob_spec(nums@, 0, n - 2);
                let r2 = Self::rob_spec(nums@, 1, n - 1);
                if r1 > r2 { r1 } else { r2 }
            },
    {
        let n = nums.len();
        if n == 1 {
            return nums[0];
        }
        let hi1: usize = n - 2;
        let rob1: i32;
        if hi1 == 0 {
            rob1 = nums[0];
        } else {
            proof {
                Self::rob_bounds(nums@, 0, 0);
                Self::rob_bounds(nums@, 0, 1);
            }
            let mut a: i32 = nums[0];
            let mut b: i32 = if nums[0] > nums[1] { nums[0] } else { nums[1] };
            let mut i: usize = 2;
            while i <= hi1
                invariant
                    2 <= i <= hi1 + 1,
                    hi1 == n - 2,
                    n == nums.len(),
                    1 <= n <= 100,
                    forall|j: int| 0 <= j < n ==> 0 <= #[trigger] nums@[j] <= 1000,
                    a as int == Self::rob_spec(nums@, 0, (i - 2) as int),
                    b as int == Self::rob_spec(nums@, 0, (i - 1) as int),
                    0 <= a <= 100000,
                    0 <= b <= 100000,
                decreases hi1 + 1 - i,
            {
                proof {
                    Self::rob_bounds(nums@, 0, i as int);
                    Self::rob_bounds(nums@, 0, (i - 1) as int);
                    Self::rob_bounds(nums@, 0, (i - 2) as int);
                }
                let c = if a + nums[i] > b { a + nums[i] } else { b };
                a = b;
                b = c;
                i = i + 1;
            }
            rob1 = b;
        }
        let hi2: usize = n - 1;
        let rob2: i32;
        if n == 2 {
            rob2 = nums[1];
        } else {
            proof {
                Self::rob_bounds(nums@, 1, 1);
                Self::rob_bounds(nums@, 1, 2);
            }
            let mut a: i32 = nums[1];
            let mut b: i32 = if nums[1] > nums[2] { nums[1] } else { nums[2] };
            let mut i: usize = 3;
            while i <= hi2
                invariant
                    3 <= i <= hi2 + 1,
                    hi2 == n - 1,
                    n == nums.len(),
                    1 <= n <= 100,
                    forall|j: int| 0 <= j < n ==> 0 <= #[trigger] nums@[j] <= 1000,
                    a as int == Self::rob_spec(nums@, 1, (i - 2) as int),
                    b as int == Self::rob_spec(nums@, 1, (i - 1) as int),
                    0 <= a <= 100000,
                    0 <= b <= 100000,
                decreases hi2 + 1 - i,
            {
                proof {
                    Self::rob_bounds(nums@, 1, i as int);
                    Self::rob_bounds(nums@, 1, (i - 1) as int);
                    Self::rob_bounds(nums@, 1, (i - 2) as int);
                }
                let c = if a + nums[i] > b { a + nums[i] } else { b };
                a = b;
                b = c;
                i = i + 1;
            }
            rob2 = b;
        }
        if rob1 > rob2 { rob1 } else { rob2 }
    }
}

} 
