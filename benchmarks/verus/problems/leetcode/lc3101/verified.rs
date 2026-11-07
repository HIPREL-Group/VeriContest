use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alt_end_count(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else if end > nums.len() {
            Self::alt_end_count(nums, nums.len() as int)
        } else if end == 1 {
            1
        } else if nums[end - 1] != nums[end - 2] {
            Self::alt_end_count(nums, end - 1) + 1
        } else {
            1
        }
    }

    pub open spec fn alt_total_prefix(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else if end > nums.len() {
            Self::alt_total_prefix(nums, nums.len() as int)
        } else {
            Self::alt_total_prefix(nums, end - 1) + Self::alt_end_count(nums, end)
        }
    }

    pub open spec fn count_alternating_subarrays_spec(nums: Seq<i32>) -> int {
        Self::alt_total_prefix(nums, nums.len() as int)
    }

    proof fn lemma_alt_end_step(nums: Seq<i32>, i: int)
        requires
            1 <= i < nums.len(),
        ensures
            nums[i] != nums[i - 1] ==> Self::alt_end_count(nums, i + 1) == Self::alt_end_count(nums, i) + 1,
            nums[i] == nums[i - 1] ==> Self::alt_end_count(nums, i + 1) == 1,
    {
        reveal_with_fuel(Solution::alt_end_count, 2);
    }

    proof fn lemma_alt_total_step(nums: Seq<i32>, i: int)
        requires
            0 <= i < nums.len(),
        ensures
            Self::alt_total_prefix(nums, i + 1) == Self::alt_total_prefix(nums, i) + Self::alt_end_count(nums, i + 1),
    {
        reveal_with_fuel(Solution::alt_total_prefix, 2);
    }

    pub fn count_alternating_subarrays(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || #[trigger] nums[i] == 1),
        ensures
            result as int == Self::count_alternating_subarrays_spec(nums@),
    {
        let n = nums.len();
        let mut result: i64 = 0;
        let mut cur: i64 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100000,
                forall |k: int| 0 <= k < nums.len() ==> (#[trigger] nums[k] == 0 || #[trigger] nums[k] == 1),
                0 <= i <= n,
                0 <= cur as int <= i as int,
                0 <= result as int <= i as int * 100000,
                cur as int == Self::alt_end_count(nums@, i as int),
                result as int == Self::alt_total_prefix(nums@, i as int),
            decreases n - i,
        {
            let ghost old_cur = cur as int;
            let ghost old_result = result as int;

            if i == 0 {
                cur = 1;
                proof {
                    assert(Self::alt_end_count(nums@, 1) == 1);
                    assert(cur as int == Self::alt_end_count(nums@, i as int + 1));
                }
            } else if nums[i] != nums[i - 1] {
                proof {
                    Self::lemma_alt_end_step(nums@, i as int);
                }
                cur = cur + 1;
                proof {
                    assert(old_cur == Self::alt_end_count(nums@, i as int));
                    assert(cur as int == old_cur + 1);
                    assert(Self::alt_end_count(nums@, i as int + 1) == Self::alt_end_count(nums@, i as int) + 1);
                    assert(cur as int == Self::alt_end_count(nums@, i as int + 1));
                }
            } else {
                proof {
                    Self::lemma_alt_end_step(nums@, i as int);
                }
                cur = 1;
                proof {
                    assert(Self::alt_end_count(nums@, i as int + 1) == 1);
                    assert(cur as int == Self::alt_end_count(nums@, i as int + 1));
                }
            }

            proof {
                assert(0 <= cur as int <= i as int + 1);
            }

            result = result + cur;

            proof {
                Self::lemma_alt_total_step(nums@, i as int);
                assert(old_result == Self::alt_total_prefix(nums@, i as int));
                assert(result as int == old_result + cur as int);
                assert(Self::alt_total_prefix(nums@, i as int + 1)
                    == Self::alt_total_prefix(nums@, i as int) + Self::alt_end_count(nums@, i as int + 1));
                assert(result as int == Self::alt_total_prefix(nums@, i as int + 1));
                assert(0 <= result as int <= (i as int + 1) * 100000);
            }

            i = i + 1;
        }

        result
    }
}

}
