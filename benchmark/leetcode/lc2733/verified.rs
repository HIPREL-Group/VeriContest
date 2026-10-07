use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_non_min_or_max(nums: Vec<i32>) -> (res: i32) 
        requires 
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures 
            nums.len() < 3 ==> res == -1,
            nums.len() >= 3 ==> {
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] == res
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] < res
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] > res
            },
    {
        if nums.len() < 3 {
            return -1;
        }

        let mut min_val = nums[0];
        let mut max_val = nums[0];

        let mut i = 1;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
                forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
                1 <= i <= nums.len(),
                1 <= min_val <= 100,
                1 <= max_val <= 100,
                exists|idx: int| 0 <= idx < i && nums[idx] == min_val,
                exists|idx: int| 0 <= idx < i && nums[idx] == max_val,
                forall|j: int| 0 <= j < i ==> min_val <= nums[j],
                forall|j: int| 0 <= j < i ==> nums[j] <= max_val,
            decreases nums.len() - i,
        {
            if nums[i] < min_val {
                min_val = nums[i];
            }
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        
        let mut j = 0;
        while j < nums.len()
            invariant
                1 <= nums.len() <= 100,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
                forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
                0 <= j <= nums.len(),
                1 <= min_val <= 100,
                1 <= max_val <= 100,
                exists|idx: int| 0 <= idx < nums.len() && nums[idx] == min_val,
                exists|idx: int| 0 <= idx < nums.len() && nums[idx] == max_val,
                forall|k: int| 0 <= k < nums.len() ==> min_val <= #[trigger] nums[k] <= max_val,
                forall|k: int| 0 <= k < j ==> nums[k] == min_val || nums[k] == max_val,
            decreases nums.len() - j,
        {
            if nums[j] != min_val && nums[j] != max_val {
                return nums[j];
            }
            j += 1;
        }

        proof {
            let idx_min = choose|idx: int| 0 <= idx < nums.len() && nums[idx] == min_val;
            assert(0 <= idx_min < nums.len() && nums[idx_min] == min_val);

            let idx_max = choose|idx: int| 0 <= idx < nums.len() && nums[idx] == max_val;
            assert(0 <= idx_max < nums.len() && nums[idx_max] == max_val);
            
            let idx_third = if idx_min != 0 && idx_max != 0 {
                0
            } else if idx_min != 1 && idx_max != 1 {
                1
            } else {
                2
            };
            
            assert(nums[idx_third] == min_val || nums[idx_third] == max_val);
        }

        -1
    }
}

}