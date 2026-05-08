use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_len_at_most(nums: Seq<i32>, bound: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else if nums[n - 1] as int <= bound {
            Self::suffix_len_at_most(nums, bound, n - 1) + 1
        } else {
            0
        }
    }

    pub open spec fn count_at_most(nums: Seq<i32>, bound: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_at_most(nums, bound, n - 1)
                + Self::suffix_len_at_most(nums, bound, n)
        }
    }

    pub open spec fn count_bounded_max(nums: Seq<i32>, left: int, right: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
            left <= right,
    {
        Self::count_at_most(nums, right, n) - Self::count_at_most(nums, left - 1, n)
    }

    fn count_at_most_exec(nums: &Vec<i32>, bound: i32) -> (ans: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            ans >= 0,
            ans as int == Self::count_at_most(nums@, bound as int, nums.len() as int),
    {
        let n = nums.len();
        let mut ans: i64 = 0;
        let mut cnt: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let prev_ans = ans;
            let prev_cnt = cnt;
            let value = nums[i];
            if value <= bound {
                cnt = cnt + 1;
            } else {
                cnt = 0;
            }
            ans = ans + cnt;
            i = i + 1;
        }
        ans
    }

    pub fn num_subarray_bounded_max(nums: Vec<i32>, left: i32, right: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= left <= right <= 1_000_000_000,
            Self::count_bounded_max(nums@, left as int, right as int, nums.len() as int) <= i32::MAX,
        ensures
            res as int == Self::count_bounded_max(nums@, left as int, right as int, nums.len() as int),
    {
        let upper = Self::count_at_most_exec(&nums, right);
        let lower = Self::count_at_most_exec(&nums, left - 1);
        let result = upper - lower;
        result as i32
    }
}

}
