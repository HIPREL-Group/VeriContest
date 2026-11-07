use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_rotation_point(nums: Seq<i32>, k: int) -> bool {
        0 <= k < nums.len()
        && (forall |a: int, b: int| k <= a < b < nums.len() ==> nums[a] <= nums[b])
        && (forall |a: int, b: int| 0 <= a < b < k ==> nums[a] <= nums[b])
        && (k == 0 || forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() ==> nums[a] >= nums[b])
    }

    pub fn find_min(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 5000,
            forall |i: int| 0 <= i < nums.len() ==> -5000 <= #[trigger] nums[i] <= 5000,
            exists |k: int| Self::is_rotation_point(nums@, k),
        ensures
            forall |i: int| 0 <= i < nums.len() ==> result <= nums[i],
            exists |i: int| 0 <= i < nums.len() && result == nums[i],
    {
        let ghost mut min_idx: int;

        proof {
            let k = choose |k: int| Self::is_rotation_point(nums@, k);
            assert forall |j: int| 0 <= j < nums.len() implies nums[k] <= nums[j] by {
                if j >= k {
                    if j > k {  }
                } else {
                    
                }
            };
            min_idx = k;
        }

        let mut left: usize = 0;
        let mut right: usize = nums.len() - 1;

        while left < right
            invariant
                0 <= left <= right < nums.len(),
                left as int <= min_idx <= right as int,
                1 <= nums.len() <= 5000,
                forall |i: int| 0 <= i < nums.len() ==> -5000 <= #[trigger] nums[i] <= 5000,
                exists |k: int| Self::is_rotation_point(nums@, k),
                forall |j: int| 0 <= j < nums.len() ==> nums[min_idx] <= nums[j],
            decreases right - left,
        {
            let mid = left + (right - left) / 2;

            if nums[mid] > nums[right] {
                proof {
                    let rk = choose |k: int| Self::is_rotation_point(nums@, k);
                    
                    
                    if rk <= mid as int {
                        assert(nums[mid as int] <= nums[right as int]);
                    }
                    
                    
                    if rk > right as int {
                        assert(nums[mid as int] <= nums[right as int]);
                    }
                    
                    assert forall |j: int| 0 <= j < nums.len() implies nums[rk] <= nums[j] by {
                        if j >= rk {} else {}
                    };
                    min_idx = rk;
                }
                left = mid + 1;
            } else if nums[mid] < nums[right] {
                proof {
                    let rk = choose |k: int| Self::is_rotation_point(nums@, k);
                    
                    
                    if rk > mid as int && rk <= right as int {
                        assert(nums[mid as int] >= nums[right as int]);
                    }
                    
                    
                    
                    if rk > right as int || rk < left as int {
                        
                        assert(nums[left as int] <= nums[min_idx]);
                        min_idx = left as int;
                    } else {
                        
                        assert forall |j: int| 0 <= j < nums.len() implies nums[rk] <= nums[j] by {
                            if j >= rk {} else {}
                        };
                        min_idx = rk;
                    }
                }
                right = mid;
            } else {
                
                proof {
                    if min_idx == right as int {
                        
                        
                        min_idx = mid as int;
                    }
                }
                right = right - 1;
            }
        }

        proof {
            assert(left as int == min_idx);
            assert forall |i: int| 0 <= i < nums.len() implies nums[left as int] <= nums[i] by {
                assert(nums[min_idx] <= nums[i]);
            };
        }

        nums[left]
    }
}

}
