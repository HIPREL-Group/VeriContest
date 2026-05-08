use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_in_range(nums: Seq<i32>, start: int, end: int, value: int) -> bool {
        exists |k: int| start <= k < end && #[trigger] nums[k] as int == value
    }

    pub open spec fn distinct_count(nums: Seq<i32>, start: int, end: int, value: int) -> int
        decreases value,
    {
        if value <= 0 {
            0
        } else {
            Self::distinct_count(nums, start, end, value - 1)
                + if Self::contains_in_range(nums, start, end, value) { 1int } else { 0int }
        }
    }

    pub open spec fn subarray_score(nums: Seq<i32>, start: int, end: int) -> int {
        let d = Self::distinct_count(nums, start, end, 100);
        d * d
    }

    pub open spec fn sum_end_until(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if end <= start {
            0
        } else {
            Self::sum_end_until(nums, start, end - 1) + Self::subarray_score(nums, start, end)
        }
    }

    pub open spec fn sum_starts_prefix(nums: Seq<i32>, upto: int) -> int
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::sum_starts_prefix(nums, upto - 1) + Self::sum_end_until(nums, upto - 1, nums.len() as int)
        }
    }

    fn contains_range(nums: &Vec<i32>, start: usize, end: usize, value: i32) -> (found: bool)
        ensures
            found == Self::contains_in_range(nums@, start as int, end as int, value as int),
    {
        let mut k: usize = start;
        let mut found = false;
        while k < end {
            if nums[k] == value {
                found = true;
            }
            k = k + 1;
        }
        found
    }

    fn distinct_count_range(nums: &Vec<i32>, start: usize, end: usize) -> (count: i32)
        ensures
            count as int == Self::distinct_count(nums@, start as int, end as int, 100),
    {
        let mut value: i32 = 1;
        let mut count: i32 = 0;
        while value <= 100 {
            if Self::contains_range(nums, start, end, value) {
                count = count + 1;
            }
            value = value + 1;
        }
        count
    }

    pub fn sum_counts(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::sum_starts_prefix(nums@, nums.len() as int),
    {
        let n: usize = nums.len();
        let mut i: usize = 0;
        let mut total: i32 = 0;
        while i < n {
            let mut end: usize = i + 1;
            let mut row_sum: i32 = 0;
            while end <= n {
                let d = Self::distinct_count_range(&nums, i, end);
                row_sum = row_sum + d * d;
                end = end + 1;
            }
            total = total + row_sum;
            i = i + 1;
        }
        total
    }
}

}
