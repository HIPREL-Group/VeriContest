use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cmp(a: i32, b: i32) -> int {
        if b > a { 1 } else if b < a { -1 } else { 0 }
    }

    pub open spec fn subarray_matches(nums: Seq<i32>, pattern: Seq<i32>, start: int) -> bool {
        forall |k: int| 0 <= k < pattern.len() ==> #[trigger] pattern[k] == Self::cmp(nums[start + k], nums[start + k + 1])
    }

    pub open spec fn count_prefix(nums: Seq<i32>, pattern: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_prefix(nums, pattern, end - 1)
                + if Self::subarray_matches(nums, pattern, end - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn count_matching_subarrays_spec(nums: Seq<i32>, pattern: Seq<i32>) -> int {
        Self::count_prefix(nums, pattern, nums.len() as int - pattern.len() as int)
    }

    pub fn count_matching_subarrays(nums: Vec<i32>, pattern: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            1 <= pattern.len() < nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < pattern.len() ==> -1 <= #[trigger] pattern[i] <= 1,
        ensures
            result as int == Self::count_matching_subarrays_spec(nums@, pattern@),
    {
        let n = nums.len();
        let m = pattern.len();
        let mut ans: i32 = 0;

        let mut i: usize = 0;
        while i + m < n
            decreases n - (i + m),
        {
            let mut ok = true;
            let mut k: usize = 0;
            while k < m
                decreases m - k,
            {
                let idx = i + k;
                let d = if nums[idx + 1] > nums[idx] {
                    1
                } else if nums[idx + 1] < nums[idx] {
                    -1
                } else {
                    0
                };
                let pk = pattern[k];
                if d != pk {
                    ok = false;
                }
                k += 1;
            }
            if ok {
                ans += 1;
            }
            i += 1;
        }

        ans
    }
}

}
