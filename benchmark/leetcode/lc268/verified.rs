use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains(nums: Seq<i32>, value: i32) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == value
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn missing_number(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= nums.len(),
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j], 
            exists |k: int| 0 <= k <= nums.len() && !(#[trigger] Self::contains(nums@, k as i32)),
        ensures 
            0 <= res <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> nums[i] != res, 
    {
        let n = nums.len() as i32;
        let mut candidate = 0;
        let mut found_missing = false;
        
        while candidate <= n && !found_missing
            invariant
                n == nums.len(),
                0 <= candidate <= n + 1,
                1 <= nums.len() <= 10_000,
                forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= nums.len(),
                forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
                exists |k: int| 0 <= k <= nums.len() && !(#[trigger] Self::contains(nums@, k as i32)),
                forall |k: int| 0 <= k < candidate ==> #[trigger] Self::contains(nums@, k as i32),
                found_missing ==> (0 <= candidate <= nums.len() && forall |j: int| 0 <= j < nums.len() ==> nums[j] != candidate),
        {
            let mut exists_in_nums = false;
            let mut ix = 0;
            
            while ix < nums.len() && !exists_in_nums
                invariant
                    n == nums.len(),
                    0 <= candidate <= n + 1,
                    1 <= nums.len() <= 10_000,
                    forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= nums.len(),
                    forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
                    exists |k: int| 0 <= k <= nums.len() && !(#[trigger] Self::contains(nums@, k as i32)),
                    forall |k: int| 0 <= k < candidate ==> #[trigger] Self::contains(nums@, k as i32),
                    found_missing ==> (0 <= candidate <= nums.len() && forall |j: int| 0 <= j < nums.len() ==> nums[j] != candidate),
                    0 <= ix <= nums.len(),
                    exists_in_nums ==> exists |j: int| 0 <= j < ix && nums[j] == candidate,
                    !exists_in_nums ==> forall |j: int| 0 <= j < ix ==> nums[j] != candidate,
            {
                if nums[ix] == candidate {
                    exists_in_nums = true;
                }
                ix += 1;
            }
            
            if !exists_in_nums {
                found_missing = true;
            } else {
                candidate += 1;
            }
        }

        candidate
    }
}

}