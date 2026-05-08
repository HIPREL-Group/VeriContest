use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_ge_k(nums: Seq<i32>, k: int) -> bool {
        forall |i: int| 0 <= i < nums.len() ==> nums[i] as int >= k
    }

    pub open spec fn value_present(nums: Seq<i32>, v: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] as int == v
    }

    pub open spec fn count_distinct_in_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            0
        } else {
            (if Self::value_present(nums, start) { 1int } else { 0int })
                + Self::count_distinct_in_range(nums, start + 1, end)
        }
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            -1 <= res <= 100,
            Self::all_ge_k(nums@, k as int) ==> res as int == Self::count_distinct_in_range(nums@, k as int + 1, 101),
            !Self::all_ge_k(nums@, k as int) ==> res == -1,
    {
        let mut i: usize = 0;
        while i < nums.len() {
            let x = nums[i];
            if x < k {
                return -1;
            }
            i = i + 1;
        }

        let mut ans: i32 = 0;
        let mut value: i32 = k + 1;
        while value <= 100 {
            let mut found: bool = false;
            let mut j: usize = 0;
            while j < nums.len() {
                if nums[j] == value {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                ans = ans + 1;
            }
            value = value + 1;
        }

        ans
    }
}

}
