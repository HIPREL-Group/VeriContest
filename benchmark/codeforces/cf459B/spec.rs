use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn is_minimum(nums: Seq<i64>, mn: int) -> bool {
    nums.len() > 0
        && exists|i: int| 0 <= i < nums.len() && nums[i] as int == mn
        && forall|j: int| 0 <= j < nums.len() ==> mn <= #[trigger] nums[j] as int
}

pub open spec fn is_maximum(nums: Seq<i64>, mx: int) -> bool {
    nums.len() > 0
        && exists|i: int| 0 <= i < nums.len() && nums[i] as int == mx
        && forall|j: int| 0 <= j < nums.len() ==> #[trigger] nums[j] as int <= mx
}

pub open spec fn count_value_up_to(nums: Seq<i64>, value: int, end: int) -> nat
    recommends 0 <= end <= nums.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_value_up_to(nums, value, end - 1)
            + if nums[end - 1] as int == value { 1nat } else { 0nat }
    }
}

pub open spec fn count_value(nums: Seq<i64>, value: int) -> nat {
    count_value_up_to(nums, value, nums.len() as int)
}

pub open spec fn is_extremal_pair_for(nums: Seq<i64>, mn: int, mx: int, i: int, j: int) -> bool {
    &&& 0 <= i < j < nums.len()
    &&& (
        (nums[i] as int == mn && nums[j] as int == mx)
        || (nums[i] as int == mx && nums[j] as int == mn)
    )
}

pub open spec fn count_extremal_pairs_for_with_right(nums: Seq<i64>, mn: int, mx: int, right: int, left_end: int) -> nat
    recommends 0 <= left_end <= right < nums.len(),
    decreases left_end,
{
    if left_end <= 0 {
        0
    } else {
        count_extremal_pairs_for_with_right(nums, mn, mx, right, left_end - 1)
            + if is_extremal_pair_for(nums, mn, mx, left_end - 1, right) { 1nat } else { 0nat }
    }
}

pub open spec fn count_extremal_pairs_for_up_to(nums: Seq<i64>, mn: int, mx: int, end: int) -> nat
    recommends 0 <= end <= nums.len(),
    decreases end,
{
    if end <= 1 {
        0
    } else {
        count_extremal_pairs_for_up_to(nums, mn, mx, end - 1)
            + count_extremal_pairs_for_with_right(nums, mn, mx, end - 1, end - 1)
    }
}

impl Solution {
    pub fn max_beauty_and_pair_count(flowers: Vec<i64>) -> (result: (i64, i64))
        requires
            2 <= flowers.len() <= 200_000,
            forall|i: int| 0 <= i < flowers.len() ==> 1 <= #[trigger] flowers[i] <= 1_000_000_000,
        ensures
            exists|mn: int, mx: int| {
                &&& is_minimum(flowers@, mn)
                &&& is_maximum(flowers@, mx)
                &&& result.0 as int == mx - mn
                &&& result.1 as int == count_extremal_pairs_for_up_to(flowers@, mn, mx, flowers.len() as int)
                &&& forall|i: int, j: int|
                    0 <= i < j < flowers.len() ==> (
                        #[trigger] is_extremal_pair_for(flowers@, mn, mx, i, j)
                        <==> abs_diff(flowers[i] as int, flowers[j] as int) == result.0 as int
                    )
            },
    {
    }
}

}
