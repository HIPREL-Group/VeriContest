use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_j(nums: Seq<i32>, target: i32, i: int, j: int) -> int
        recommends
            0 <= i < nums.len(),
            0 <= j <= nums.len(),
        decreases if j > i { j - i } else { 0int },
    {
        if j <= i + 1 {
            0
        } else {
            Self::count_j(nums, target, i, j - 1) + (if nums[i] + nums[j - 1] < target { 1int } else { 0int })
        }
    }

    pub open spec fn count_i(nums: Seq<i32>, target: i32, i: int) -> int
        recommends
            0 <= i <= nums.len(),
        decreases if i > 0 { i } else { 0int },
    {
        if i <= 0 {
            0
        } else {
            Self::count_i(nums, target, i - 1) + Self::count_j(nums, target, i - 1, nums.len() as int)
        }
    }

    pub fn count_pairs(nums: Vec<i32>, target: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            -50 <= target <= 50,
            forall|k: int| 0 <= k < nums.len() ==> -50 <= #[trigger] nums[k] <= 50,
        ensures
            result == Self::count_i(nums@, target, nums.len() as int),
    {
        let mut count: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();
        
        while i < n {
            let mut j: usize = i + 1;
            let mut inner_count: i32 = 0;
            
            while j < n {
                if nums[i] + nums[j] < target {
                    inner_count += 1;
                }
                j += 1;
            }
            count += inner_count;
            i += 1;
        }
        
        count
    }
}

}
