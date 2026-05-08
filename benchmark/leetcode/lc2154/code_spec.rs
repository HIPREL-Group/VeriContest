use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub open spec fn chain_value(original: i32, k: nat) -> int {
        original as int * pow(2, k)
    }

    pub open spec fn appears(nums: Seq<i32>, v: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && #[trigger] nums[i] == v
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn find_final_value(nums: Vec<i32>, original: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            1 <= original <= 1000,
        ensures
            exists |k: nat|
                result as int == Self::chain_value(original, k)
                && forall |t: nat| t < k ==> #[trigger] Self::appears(nums@, Self::chain_value(original, t))
                && forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != result,
    {
        let mut current = original;
        let mut found = true;
        while found {
            found = false;
            let mut i = 0;
            while i < nums.len() {
                if nums[i] == current {
                    found = true;
                }
                i += 1;
            }
            if found {
                current *= 2;
            }
        }
        current
    }
}
}
