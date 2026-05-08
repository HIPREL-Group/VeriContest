use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn valid_split(nums: Seq<i32>, i: int) -> bool {
        if 0 <= i < nums.len() - 1 {
            let left = Self::prefix_sum(nums, i + 1);
            left >= Self::prefix_sum(nums, nums.len() as int) - left
        } else {
            false
        }
    }

    pub open spec fn count_valid_splits(nums: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto,
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::count_valid_splits(nums, upto - 1)
                + if Self::valid_split(nums, upto - 1) { 1int } else { 0int }
        }
    }

    proof fn lemma_prefix_sum_step(nums: Seq<i32>, i: int)
        requires
            0 <= i < nums.len(),
        ensures
            Self::prefix_sum(nums, i + 1) == Self::prefix_sum(nums, i) + nums[i] as int,
    {
    }

    proof fn lemma_count_valid_splits_step(nums: Seq<i32>, upto: int)
        requires
            0 <= upto,
        ensures
            Self::count_valid_splits(nums, upto + 1)
                == Self::count_valid_splits(nums, upto)
                    + if Self::valid_split(nums, upto) { 1int } else { 0int },
    {
    }

    pub fn ways_to_split_array(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            0 <= result as int <= nums.len() as int - 1,
            result as int == Self::count_valid_splits(nums@, nums.len() as int - 1),
    {
        let n = nums.len();
        let mut total: i128 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                0 <= i <= n,
                forall |k: int| 0 <= k < n ==> -100_000 <= #[trigger] nums[k] <= 100_000,
                total as int == Self::prefix_sum(nums@, i as int),
                -100_000 * (i as int) <= total as int <= 100_000 * (i as int),
            decreases n - i,
        {
            proof {
                Self::lemma_prefix_sum_step(nums@, i as int);
            }
            total = total + nums[i] as i128;
            i += 1;
        }

        let mut left_sum: i128 = 0;
        let mut count: i32 = 0;
        i = 0;

        while i < n - 1
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                0 <= i <= n - 1,
                forall |k: int| 0 <= k < n ==> -100_000 <= #[trigger] nums[k] <= 100_000,
                total as int == Self::prefix_sum(nums@, n as int),
                -100_000 * (n as int) <= total as int <= 100_000 * (n as int),
                left_sum as int == Self::prefix_sum(nums@, i as int),
                -100_000 * (i as int) <= left_sum as int <= 100_000 * (i as int),
                count as int == Self::count_valid_splits(nums@, i as int),
                0 <= count as int <= i as int,
            decreases n - 1 - i,
        {
            proof {
                Self::lemma_prefix_sum_step(nums@, i as int);
            }
            left_sum = left_sum + nums[i] as i128;
            proof {
                assert(left_sum as int == Self::prefix_sum(nums@, i as int + 1));
                assert(-100_000 * (i as int + 1) <= left_sum as int <= 100_000 * (i as int + 1));
                assert(-20_000_000_000int <= (total as int) - (left_sum as int) <= 20_000_000_000int);
            }
            let right_sum = total - left_sum;
            if left_sum >= right_sum {
                proof {
                    assert(total as int == Self::prefix_sum(nums@, n as int));
                    assert(right_sum as int == total as int - left_sum as int);
                    assert(left_sum as int >= right_sum as int);
                    assert(Self::valid_split(nums@, i as int));
                    Self::lemma_count_valid_splits_step(nums@, i as int);
                    assert(count as int + 1 == Self::count_valid_splits(nums@, i as int + 1));
                    assert(count < 2_147_483_647);
                }
                count = count + 1;
            } else {
                proof {
                    assert(total as int == Self::prefix_sum(nums@, n as int));
                    assert(right_sum as int == total as int - left_sum as int);
                    assert(left_sum < right_sum);
                    assert((left_sum as int) < (right_sum as int));
                    assert(!Self::valid_split(nums@, i as int));
                    Self::lemma_count_valid_splits_step(nums@, i as int);
                    assert(count as int == Self::count_valid_splits(nums@, i as int + 1));
                }
            }
            i += 1;
        }

        count
    }
}

}
