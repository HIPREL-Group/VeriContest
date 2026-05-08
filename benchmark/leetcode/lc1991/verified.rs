use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_range(nums: Seq<i32>, lo: int, hi: int) -> int
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else { nums[lo] as int + Self::sum_range(nums, lo + 1, hi) }
    }

    proof fn sum_range_split(nums: Seq<i32>, lo: int, mid: int, hi: int)
        requires
            0 <= lo <= mid <= hi <= nums.len(),
        ensures
            Self::sum_range(nums, lo, hi) == Self::sum_range(nums, lo, mid) + Self::sum_range(nums, mid, hi),
        decreases mid - lo,
    {
        if lo < mid {
            Self::sum_range_split(nums, lo + 1, mid, hi);
        }
    }

    pub fn find_middle_index(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == -1 || 0 <= result < nums.len(),
            result >= 0 ==> Self::sum_range(nums@, 0, result as int) == Self::sum_range(nums@, result as int + 1, nums.len() as int),
            result >= 0 ==> forall |j: int| 0 <= j < result as int ==>
                Self::sum_range(nums@, 0, j) != Self::sum_range(nums@, j + 1, nums.len() as int),
            result == -1 ==> forall |j: int| 0 <= j < nums.len() as int ==>
                Self::sum_range(nums@, 0, j) != Self::sum_range(nums@, j + 1, nums.len() as int),
    {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 100,
                forall |k: int| 0 <= k < nums.len() ==> -1000 <= #[trigger] nums[k] <= 1000,
                total as int == Self::sum_range(nums@, 0, i as int),
                -1000 * (i as int) <= total as int <= 1000 * (i as int),
            decreases n - i,
        {
            proof {
                assert(Self::sum_range(nums@, i as int + 1, i as int + 1) == 0int);
                Self::sum_range_split(nums@, 0, i as int, (i + 1) as int);
            }
            total = total + nums[i];
            i = i + 1;
        }
        let mut left_sum: i32 = 0;
        i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 100,
                forall |k: int| 0 <= k < nums.len() ==> -1000 <= #[trigger] nums[k] <= 1000,
                left_sum as int == Self::sum_range(nums@, 0, i as int),
                total as int == Self::sum_range(nums@, 0, n as int),
                -1000 * (i as int) <= left_sum as int <= 1000 * (i as int),
                -1000 * (n as int) <= total as int <= 1000 * (n as int),
                forall |j: int| 0 <= j < i as int ==>
                    Self::sum_range(nums@, 0, j) != Self::sum_range(nums@, j + 1, n as int),
            decreases n - i,
        {
            proof {
                Self::sum_range_split(nums@, 0, i as int, n as int);
                assert(Self::sum_range(nums@, i as int, n as int) == nums@[i as int] as int + Self::sum_range(nums@, i as int + 1, n as int));
                assert(Self::sum_range(nums@, i as int + 1, n as int) == total as int - left_sum as int - nums@[i as int] as int);
            }
            if left_sum == total - left_sum - nums[i] {
                return i as i32;
            }
            proof {
                assert(Self::sum_range(nums@, i as int + 1, i as int + 1) == 0int);
                Self::sum_range_split(nums@, 0, i as int, (i + 1) as int);
            }
            left_sum = left_sum + nums[i];
            i = i + 1;
        }
        -1
    }
}

}