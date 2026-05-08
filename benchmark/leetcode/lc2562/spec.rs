use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn concat_num_spec(left: int, right: int) -> int {
        if right < 10 {
            left * 10 + right
        } else if right < 100 {
            left * 100 + right
        } else if right < 1000 {
            left * 1000 + right
        } else if right < 10000 {
            left * 10000 + right
        } else {
            left * 100000 + right
        }
    }

    pub open spec fn conc_val_taken(nums: Seq<i32>, taken: nat) -> int
        recommends taken as int <= nums.len() / 2,
        decreases taken,
    {
        if taken == 0 {
            0
        } else {
            Self::conc_val_taken(nums, (taken - 1) as nat)
                + Self::concat_num_spec(
                    nums[(taken - 1) as int] as int,
                    nums[nums.len() - taken as int] as int,
                )
        }
    }

    pub open spec fn conc_val_spec(nums: Seq<i32>) -> int {
        let taken = (nums.len() / 2) as nat;
        if nums.len() % 2 == 0 {
            Self::conc_val_taken(nums, taken)
        } else {
            Self::conc_val_taken(nums, taken) + nums[(nums.len() / 2) as int] as int
        }
    }
}

impl Solution {
    pub fn find_the_array_conc_val(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            result as int == Self::conc_val_spec(nums@),
    {
    }
}

}
