use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(nums: Seq<i32>, i: nat, cur: nat, best: nat) -> nat
        recommends
            i <= nums.len(),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            best
        } else {
            let cur2 = if nums[i as int] == 1 { cur + 1 } else { 0 };
            let best2 = if best < cur2 { cur2 } else { best };
            Self::scan_spec(nums, i + 1, cur2, best2)
        }
    }

    pub open spec fn find_max_consecutive_ones_spec(nums: Seq<i32>) -> nat {
        Self::scan_spec(nums, 0, 0, 0)
    }

    pub fn find_max_consecutive_ones(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] == 0 || nums[i] == 1,
        ensures
            0 <= res,
            res as nat == Self::find_max_consecutive_ones_spec(nums@),
    {
        let mut i: usize = 0;
        let mut cur: i32 = 0;
        let mut best: i32 = 0;

        while i < nums.len() {
            let x = nums[i];
            if x == 1 {
                cur = cur + 1;
                if best < cur {
                    best = cur;
                }
            } else {
                cur = 0;
            }
            i = i + 1;
        }

        best
    }
}

} 
