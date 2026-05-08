use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn next_diff_or_len(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
        decreases nums.len() - i,
    {
        if i + 1 >= nums.len() {
            nums.len() as int
        } else if nums[i + 1] != nums[i] {
            i + 1
        } else {
            Self::next_diff_or_len(nums, i + 1)
        }
    }

    pub open spec fn is_hv_start(nums: Seq<i32>, i: int) -> bool {
        if 1 <= i < nums.len() - 1 && nums[i] != nums[i - 1] {
            let r = Self::next_diff_or_len(nums, i);
            r < nums.len()
                && ((nums[i] > nums[i - 1] && nums[i] > nums[r])
                    || (nums[i] < nums[i - 1] && nums[i] < nums[r]))
        } else {
            false
        }
    }

    pub open spec fn count_hv_upto(nums: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 1 {
            0
        } else {
            Self::count_hv_upto(nums, k - 1) + if Self::is_hv_start(nums, k - 1) { 1int } else { 0int }
        }
    }

    proof fn lemma_next_diff_or_len(nums: Seq<i32>, i: int, r: int)
        requires
            0 <= i < nums.len(),
            i + 1 <= r <= nums.len(),
            forall |k: int| i + 1 <= k < r ==> nums[k] == nums[i],
            r == nums.len() || nums[r] != nums[i],
        ensures
            Self::next_diff_or_len(nums, i) == r,
        decreases r - i,
    {
        if i + 1 == r {
            if r < nums.len() {
                assert(nums[i + 1] != nums[i]);
            }
        } else {
            assert(i + 1 < r);
            assert(nums[i + 1] == nums[i]);
            assert forall |k: int| i + 2 <= k < r implies #[trigger] nums[k] == nums[i + 1] by {
                assert(nums[k] == nums[i]);
            }
            Self::lemma_next_diff_or_len(nums, i + 1, r);
        }
    }

    pub fn count_hill_valley(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::count_hv_upto(nums@, nums.len() as int - 1),
            0 <= result <= nums.len(),
    {
        let n = nums.len();
        let mut i: usize = 1;
        let mut count: i32 = 0;

        while i + 1 < n
            invariant
                3 <= n <= 100,
                n == nums.len(),
                1 <= i < n,
                count as int == Self::count_hv_upto(nums@, i as int),
                0 <= count <= i,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
            decreases n - i,
        {
            let old_i = i;
            let old_count = count;

            if nums[i] == nums[i - 1] {
                i = i + 1;
                proof {
                    assert(!Self::is_hv_start(nums@, old_i as int));
                    assert(Self::count_hv_upto(nums@, i as int)
                        == Self::count_hv_upto(nums@, old_i as int)
                            + if Self::is_hv_start(nums@, old_i as int) { 1int } else { 0int });
                    assert(count == old_count);
                }
                continue;
            }

            let mut r = i + 1;
            while r < n && nums[r] == nums[i]
                invariant
                    i + 1 <= r <= n,
                    n == nums.len(),
                    1 <= i < n,
                    nums@[i as int] != nums@[i as int - 1],
                    forall |k: int| i + 1 <= k < r ==> nums@[k] == nums@[i as int],
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                decreases n - r,
            {
                r = r + 1;
            }

            if r < n {
                if (nums[i] > nums[i - 1] && nums[i] > nums[r])
                    || (nums[i] < nums[i - 1] && nums[i] < nums[r])
                {
                    count = count + 1;
                }
            }

            i = i + 1;
            proof {
                assert(r == n || nums@[r as int] != nums@[old_i as int]);
                Self::lemma_next_diff_or_len(nums@, old_i as int, r as int);
                assert(Self::count_hv_upto(nums@, i as int)
                    == Self::count_hv_upto(nums@, old_i as int)
                        + if Self::is_hv_start(nums@, old_i as int) { 1int } else { 0int });
                if count == old_count + 1 {
                    assert(Self::is_hv_start(nums@, old_i as int));
                } else {
                    assert(count == old_count);
                    assert(!Self::is_hv_start(nums@, old_i as int));
                }
            }
        }

        count
    }
}

}
