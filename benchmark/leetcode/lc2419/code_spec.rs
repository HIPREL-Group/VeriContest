use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_global_max(nums: Seq<i32>, value: i32) -> bool
    {
        &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] == value
        &&& forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] nums[idx] <= value
    }

    pub open spec fn is_constant_block(nums: Seq<i32>, value: i32, start: int, len: int) -> bool
    {
        &&& 0 <= start
        &&& 0 <= len
        &&& start + len <= nums.len()
        &&& forall|idx: int| start <= idx < start + len ==> #[trigger] nums[idx] == value
    }

    pub open spec fn is_constant_until(nums: Seq<i32>, value: i32, start: int, end: int) -> bool
    {
        &&& 0 <= start <= end <= nums.len()
        &&& forall|idx: int| start <= idx < end ==> #[trigger] nums[idx] == value
    }

    pub fn longest_subarray(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 1_000_000,
        ensures
            1 <= res,
            res as int <= nums.len() as int,
            exists|value: i32| {
                &&& Self::is_global_max(nums@, value)
                &&& exists|start: int| Self::is_constant_block(nums@, value, start, res as int)
                &&& forall|start: int, len: int|
                        Self::is_constant_block(nums@, value, start, len) && 1 <= len
                        ==> len <= res as int
            },
    {
        let mut max_val = nums[0];
        let mut i = 1usize;
        while i < nums.len()
            decreases nums.len() - i,
        {
            let x = nums[i];
            if x > max_val {
                max_val = x;
            }
            i = i + 1;
        }


        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len()
            decreases nums.len() - j,
        {
            let x = nums[j];

            if x == max_val {
                cur = cur + 1;
                if best < cur {
                    best = cur;
                }

            } else {
                cur = 0;
            }

            j = j + 1;
        }


        best
    }
}

}
