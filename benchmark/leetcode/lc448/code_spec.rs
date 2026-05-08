use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_contains(nums: Seq<i32>, k: i32) -> bool {
        exists|i: int| 0 <= i < nums.len() && nums[i] == k
    }

    pub open spec fn is_disappeared(nums: Seq<i32>, k: i32) -> bool {
        1 <= k <= nums.len() && !Self::seq_contains(nums, k)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn find_disappeared_numbers(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            nums.len() >= 1,
            nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
        ensures
            forall|i: int| 0 <= i < result.len() ==> #[trigger] Self::is_disappeared(nums@, result[i]),
            forall|k: int| 1 <= k <= nums.len() && Self::is_disappeared(nums@, k as i32) ==> #[trigger] Self::seq_contains(result@, k as i32),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] < #[trigger] result[j],
    {
        let n = nums.len();
        
        let mut seen: Vec<bool> = Vec::new();
        let mut idx: usize = 0;
        
        while idx < n + 1
            decreases n + 1 - idx
        {
            seen.push(false);
            idx += 1;
        }

        let mut i: usize = 0;
        while i < n
            decreases n - i
        {
            let val = nums[i] as usize;
            
            seen.set(val, true);
            
            
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n
            decreases n + 1 - k
        {
            if !seen[k] {

                
                result.push(k as i32);
                
                
            } else {
                
            }
            k += 1;
        }

        result
    }
}

} 
