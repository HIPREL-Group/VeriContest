use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn best(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn best3(a: int, b: int, c: int) -> int {
    best(a, best(b, c))
}

pub open spec fn interval_ops(nums: Seq<i32>, l: int, r: int, target: int) -> int
    decreases if l <= r { r - l + 1 } else { 0 },
{
    if l >= r {
        0
    } else {
        let a = if l + 1 <= r && (nums[l] as int + nums[l + 1] as int == target) {
            1 + interval_ops(nums, l + 2, r, target)
        } else {
            0
        };
        let b = if nums[l] as int + nums[r] as int == target {
            1 + interval_ops(nums, l + 1, r - 1, target)
        } else {
            0
        };
        let c = if l <= r - 1 && (nums[r - 1] as int + nums[r] as int == target) {
            1 + interval_ops(nums, l, r - 2, target)
        } else {
            0
        };
        best3(a, b, c)
    }
}

pub open spec fn max_operations_spec(nums: Seq<i32>) -> int {
    let n = nums.len() as int;
    let s1 = nums[0] as int + nums[1] as int;
    let s2 = nums[0] as int + nums[n - 1] as int;
    let s3 = nums[n - 2] as int + nums[n - 1] as int;
    best3(
        1 + interval_ops(nums, 2, n - 1, s1),
        1 + interval_ops(nums, 1, n - 2, s2),
        1 + interval_ops(nums, 0, n - 3, s3),
    )
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == max_operations_spec(nums@),
    {
    }
}

}
