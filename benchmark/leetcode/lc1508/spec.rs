use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subarray_sum(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end { 0 }
    else { nums[start] as int + subarray_sum(nums, start + 1, end) }
}

pub open spec fn sums_from(nums: Seq<i32>, start: int, end: int) -> Seq<i32>
    decreases nums.len() as int + 1 - end,
{
    if end > nums.len() || end <= start { Seq::<i32>::empty() }
    else {
        seq![subarray_sum(nums, start, end) as i32] + sums_from(nums, start, end + 1)
    }
}

pub open spec fn all_sums_seq(nums: Seq<i32>, i: int) -> Seq<i32>
    decreases nums.len() - i,
{
    if i >= nums.len() { Seq::<i32>::empty() }
    else {
        sums_from(nums, i, i + 1) + all_sums_seq(nums, i + 1)
    }
}

pub open spec fn spec_insert(sorted: Seq<i32>, val: i32) -> Seq<i32>
    decreases sorted.len(),
{
    if sorted.len() == 0 { seq![val] }
    else if val <= sorted[0] { seq![val] + sorted }
    else { seq![sorted[0]] + spec_insert(sorted.subrange(1, sorted.len() as int), val) }
}

pub open spec fn spec_sort(s: Seq<i32>) -> Seq<i32>
    decreases s.len(),
{
    if s.len() == 0 { Seq::<i32>::empty() }
    else { spec_insert(spec_sort(s.drop_last()), s.last()) }
}

pub open spec fn seq_sum(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end { 0 }
    else { s[start] as int + seq_sum(s, start + 1, end) }
}

impl Solution {
    pub fn range_sum(nums: Vec<i32>, n: i32, left: i32, right: i32) -> (result: i32)
        requires
            n == nums@.len(),
            1 <= nums@.len() <= 1000,
            forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 100,
            1 <= left <= right <= n * (n + 1) / 2,
        ensures
            result as int == seq_sum(
                spec_sort(all_sums_seq(nums@, 0)),
                (left - 1) as int, right as int,
            ) % 1_000_000_007,
    {

    }
}

}
