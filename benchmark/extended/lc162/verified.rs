use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_peak_element(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] != nums[i + 1],
        ensures
            0 <= result < nums.len(),
            (result == 0 || nums[result as int] > nums[result as int - 1]),
            (result == nums.len() - 1 || nums[result as int] > nums[result as int + 1]),
    {
        let n = nums.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right
            invariant
                0 <= left <= right < n,
                n == nums.len(),
                1 <= n <= 1000,
                forall |i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] != nums[i + 1],
                left == 0 || nums[left as int - 1] < nums[left as int],
                right == n - 1 || nums[right as int] > nums[right as int + 1],
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            proof {
                assert(mid < right) by {
                    assert(right - left >= 1usize);
                    assert((right - left) as int / 2 < (right - left) as int) by (nonlinear_arith)
                        requires (right - left) as int >= 1;
                }
                assert(mid + 1 <= right);
                assert(mid + 1 < n);
            }
            if nums[mid] < nums[mid + 1] {
                
                left = mid + 1;
            } else {
                proof {
                    assert(nums[mid as int] != nums[mid as int + 1]);
                    assert(nums[mid as int] > nums[mid as int + 1]);
                    
                }
                right = mid;
            }
        }
        
        proof {
            assert(left == right);
            assert(left == 0 || nums[left as int - 1] < nums[left as int]);
            assert(right == n - 1 || nums[right as int] > nums[right as int + 1]);
        }
        left as i32
    }
}

}
