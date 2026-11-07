use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn search_range(nums: Vec<i32>, target: i32) -> (result: Vec<i32>)
        requires
            0 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
            -1_000_000_000 <= target <= 1_000_000_000,
        ensures
            result.len() == 2,
            result[0] == -1i32 || result[0] >= 0,
            result[1] == -1i32 || result[1] >= 0,
            
            (forall |i: int| 0 <= i < nums.len() ==> nums[i] != target) ==> (result[0] == -1i32 && result[1] == -1i32),
            (result[0] == -1i32) ==> (forall |i: int| 0 <= i < nums.len() ==> nums[i] != target),
            
            result[0] >= 0 ==> (
                0 <= result[0] < nums.len() as i32
                && nums[result[0] as int] == target
                && (result[0] == 0i32 || nums[result[0] as int - 1] < target)
            ),
            
            result[1] >= 0 ==> (
                0 <= result[1] < nums.len() as i32
                && nums[result[1] as int] == target
                && (result[1] == nums.len() as i32 - 1 || nums[result[1] as int + 1] > target)
            ),
            
            (result[0] == -1i32) == (result[1] == -1i32),
            
            result[0] >= 0 ==> result[0] <= result[1],
    {
        let n = nums.len();
        if n == 0 {
            let mut res = Vec::new();
            res.push(-1i32);
            res.push(-1i32);
            return res;
        }

        let mut left_bound: i32 = -1;
        let mut right_bound: i32 = -1;

        
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi
            invariant
                0 <= lo <= hi <= n,
                n == nums.len(),
                n >= 1,
                forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
                forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
                -1_000_000_000 <= target <= 1_000_000_000,
                forall |i: int| 0 <= i < lo as int ==> nums[i] < target,
                forall |i: int| hi as int <= i < n as int ==> nums[i] >= target,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            if nums[mid] < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        
        let left_pos = lo;

        if left_pos < n && nums[left_pos] == target {
            left_bound = left_pos as i32;
        }

        
        lo = 0;
        hi = n;
        while lo < hi
            invariant
                0 <= lo <= hi <= n,
                n == nums.len(),
                n >= 1,
                forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
                forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
                -1_000_000_000 <= target <= 1_000_000_000,
                forall |i: int| 0 <= i < lo as int ==> nums[i] <= target,
                forall |i: int| hi as int <= i < n as int ==> nums[i] > target,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            if nums[mid] <= target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        
        let right_pos = lo;

        if right_pos > 0 && nums[right_pos - 1] == target {
            right_bound = (right_pos as i32) - 1;
        }

        proof {
            
            if left_bound >= 0 && right_bound >= 0 {
                
                
                
                assert(nums[left_bound as int] == target);
                assert(nums[right_bound as int] == target);
                assert(left_bound as int <= right_bound as int) by {
                    
                    
                    
                    
                    assert(left_bound as int == left_pos as int);
                    assert(right_bound as int == right_pos as int - 1);
                }
            }
            
            if left_bound == -1i32 {
                
                
                
                if left_pos < n {
                    assert(nums[left_pos as int] != target);
                    assert(nums[left_pos as int] >= target);
                    assert(nums[left_pos as int] > target);
                    
                    assert(forall |i: int| left_pos as int <= i < n as int ==> nums[i] >= nums[left_pos as int]);
                    assert(forall |i: int| left_pos as int <= i < n as int ==> nums[i] > target);
                }
                
                assert(forall |i: int| 0 <= i < left_pos as int ==> nums[i] < target);
                
                assert(forall |i: int| 0 <= i < n as int ==> nums[i] != target);
            }
            if right_bound == -1i32 && left_bound >= 0 {
                
                
                
                
                
                assert(nums[left_pos as int] == target);
                assert(left_pos < n);
                
                assert(forall |i: int| 0 <= i < right_pos as int ==> nums[i] <= target);
                
                assert(forall |i: int| right_pos as int <= i < n as int ==> nums[i] > target);
                
                
                assert(nums[left_pos as int] == target);
                if right_pos <= left_pos {
                    assert(right_pos as int <= left_pos as int);
                    assert(nums[left_pos as int] > target);
                    assert(false);
                }
                assert(right_pos > left_pos);
                assert(right_pos >= 1);
                
                assert(nums[(right_pos - 1) as int] <= target);
                
                assert(nums[(right_pos - 1) as int] >= nums[left_pos as int]);
                assert(nums[(right_pos - 1) as int] >= target);
                assert(nums[(right_pos - 1) as int] == target);
                assert(false); 
            }
            if left_bound == -1i32 && right_bound >= 0 {
                
                
                
                
                
                
                
                assert(nums[(right_pos - 1) as int] == target);
                assert(right_pos >= 1);
                let rp_m1 = (right_pos - 1) as int;
                if rp_m1 < left_pos as int {
                    assert(nums[rp_m1] < target);
                    assert(false);
                }
                assert(rp_m1 >= left_pos as int);
                assert(nums[left_pos as int] <= nums[rp_m1]);
                assert(nums[left_pos as int] <= target);
                assert(nums[left_pos as int] >= target);
                assert(nums[left_pos as int] == target);
                assert(left_pos < n);
                assert(false); 
            }
        }

        let mut res = Vec::new();
        res.push(left_bound);
        res.push(right_bound);
        res
    }
}

}
