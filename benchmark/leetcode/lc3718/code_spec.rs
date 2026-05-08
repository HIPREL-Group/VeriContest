use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_int(nums: Seq<i32>, value: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] as int == value
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn missing_multiple(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            result > 0,
            result as int % k as int == 0,
            !Self::contains_int(nums@, result as int),
            forall |q: int| q >= 1 && !Self::contains_int(nums@, #[trigger] (k as int * q)) ==> result as int <= k as int * q,
    {
        let n = nums.len();
        let mut t: i32 = 1;
        let mut candidate = k;

        while candidate <= 100
        {
            let mut exists = false;
            let mut i: usize = 0;
            while i < n
            {
                if nums[i] == candidate {
                    exists = true;
                }
                i += 1;
            }

            if !exists {
                return candidate;
            }

            candidate = candidate + k;
            t = t + 1;
        }

        candidate
    }
}

}
