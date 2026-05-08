use vstd::prelude::*;

verus! {




pub open spec fn spec_run(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i < 2 {
        0
    } else if nums[i] - nums[i - 1] == nums[i - 1] - nums[i - 2] {
        spec_run(nums, i - 1) + 1
    } else {
        0
    }
}


pub open spec fn spec_total(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k < 2 {
        0
    } else {
        spec_total(nums, k - 1) + spec_run(nums, k)
    }
}

pub open spec fn spec_number_of_arithmetic_slices(nums: Seq<i32>) -> int
{
    if nums.len() < 3 {
        0
    } else {
        spec_total(nums, (nums.len() - 1) as int)
    }
}

fn number_of_arithmetic_slices(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() >= 1,
        nums.len() <= 5000,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        result as int == spec_number_of_arithmetic_slices(nums@),
{
}

}
