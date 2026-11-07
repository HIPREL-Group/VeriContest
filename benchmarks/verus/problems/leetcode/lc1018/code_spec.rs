use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn binary_val(nums: Seq<i32>, len: nat) -> int
        decreases len,
    {
        if len == 0 {
            0
        } else {
            Self::binary_val(nums, (len - 1) as nat) * 2 + nums[(len - 1) as int] as int
        }
    }

    pub fn prefixes_div_by5(nums: Vec<i32>) -> (result: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
        ensures
            result.len() == nums.len(),
            forall|i: int|
                0 <= i < result.len() ==> #[trigger] result[i] == (Self::binary_val(
                    nums@,
                    (i + 1) as nat,
                ) % 5 == 0),
    {
        let mut result: Vec<bool> = Vec::new();
        let mut rem: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            rem = (rem * 2 + nums[i]) % 5;
            result.push(rem == 0);
            i += 1;
        }
        result
    }
}

}
