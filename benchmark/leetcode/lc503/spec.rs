use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn circ_idx(n: int, i: int, k: int) -> int
    decreases 0int
{
    if i + k < n {
        i + k
    } else {
        i + k - n
    }
}

pub open spec fn is_next_greater(nums: Seq<i32>, res: Seq<i32>, i: int) -> bool
    decreases 0int
{
    let n = nums.len() as int;
    0 <= i < n
    && (
        (res[i] == -1
         && forall |k: int| 1 <= k < n ==> nums[circ_idx(n, i, k)] <= nums[i])
        || (res[i] != -1
            && res[i] > nums[i]
            && exists |k: int|
                1 <= k < n
                && nums[circ_idx(n, i, k)] == res[i]
                && forall |j: int| 1 <= j < k ==> nums[circ_idx(n, i, j)] <= nums[i])
    )
}

impl Solution {
    pub fn next_greater_elements(nums: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != -1i32,
        ensures
            res.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> is_next_greater(nums@, res@, i),
    {
    }
}

}