use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_inc(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1
    } else if nums[i] > nums[i - 1] {
        spec_inc(nums, i - 1) + 1
    } else {
        1
    }
}


pub open spec fn spec_dec(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1
    } else if nums[i] < nums[i - 1] {
        spec_dec(nums, i - 1) + 1
    } else {
        1
    }
}


pub open spec fn spec_max(a: int, b: int) -> int
{
    if a >= b { a } else { b }
}


pub open spec fn spec_best(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        1
    } else {
        spec_max(
            spec_best(nums, k - 1),
            spec_max(spec_inc(nums, k), spec_dec(nums, k)),
        )
    }
}

pub open spec fn spec_longest_monotonic_subarray(nums: Seq<i32>) -> int
{
    if nums.len() == 0 {
        0
    } else {
        spec_best(nums, (nums.len() - 1) as int)
    }
}

impl Solution {
    pub fn longest_monotonic_subarray(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() > 0,
            nums.len() <= 50,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            result as int == spec_longest_monotonic_subarray(nums@),
    {
        let n = nums.len();
        if n == 0 {
            return 0;
        }
        let mut best = 1i32;
        let mut inc = 1i32;
        let mut dec = 1i32;
        let mut i = 1;
        while i < n
            decreases n - i,
        {
            if nums[i] > nums[i - 1] {
                inc = inc + 1;
            } else {
                inc = 1;
            }
            if nums[i] < nums[i - 1] {
                dec = dec + 1;
            } else {
                dec = 1;
            }
            let cur = if inc > dec { inc } else { dec };
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

}
