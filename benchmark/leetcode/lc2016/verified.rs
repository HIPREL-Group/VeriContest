use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn maximum_difference(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            res == -1 || res >= 1,
            res == -1 ==>
                forall |a: int, b: int| 0 <= a < b < nums.len() as int
                    ==> nums[a] >= nums[b],
            res >= 1 ==>
                exists |a: int, b: int| 0 <= a < b < nums.len() as int
                    && nums[a] < nums[b]
                    && res == nums[b] - nums[a],
            res >= 1 ==>
                forall |a: int, b: int| 0 <= a < b < nums.len() as int
                    && nums[a] < nums[b]
                    ==> nums[b] - nums[a] <= res,
    {
        let n = nums.len();
        let mut min_val: i64 = nums[0] as i64;
        let mut best: i64 = -1;
        let mut i: usize = 1;

        let ghost mut min_idx: int = 0;
        let ghost mut best_lo: int = 0;
        let ghost mut best_hi: int = 0;

        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                1 <= i <= n,
                
                1 <= min_val <= 1_000_000_000,
                0 <= min_idx < i,
                min_val == nums[min_idx] as i64,
                forall |k: int| 0 <= k < i ==> min_val <= nums[k] as i64,
                
                best == -1 || (1 <= best <= 999_999_999),
                
                best == -1 ==>
                    forall |a: int, b: int| 0 <= a < b < i
                        ==> nums[a] >= nums[b],
                
                best >= 1 ==> (
                    0 <= best_lo < best_hi < i
                    && nums[best_lo] < nums[best_hi]
                    && best == nums[best_hi] as i64 - nums[best_lo] as i64
                ),
                best >= 1 ==>
                    forall |a: int, b: int| 0 <= a < b < i
                        && nums[a] < nums[b]
                        ==> nums[b] as i64 - nums[a] as i64 <= best,
            decreases n - i,
        {
            if nums[i] as i64 > min_val {
                let diff = nums[i] as i64 - min_val;
                if diff > best {
                    proof {
                        best_lo = min_idx;
                        best_hi = i as int;
                    }
                    best = diff;
                }
            }

            proof {
                
                
                
                
                
                
                
                
                
                let ii = i as int;
                assert forall |a: int, b: int|
                    0 <= a < b < (ii + 1) && nums[a] < nums[b]
                implies
                    nums[b] as i64 - nums[a] as i64 <= best
                by {
                    if b < ii {
                        
                    } else {
                        
                        assert(min_val <= nums[a] as i64);
                        assert(nums[ii] as i64 - nums[a] as i64 <= nums[ii] as i64 - min_val);
                        
                        assert(nums[ii] as i64 > min_val);
                        
                    }
                }

                
                
                
                if best == -1 {
                    assert(nums[ii] as i64 <= min_val);
                    assert forall |a: int, b: int|
                        0 <= a < b < (ii + 1)
                    implies
                        nums[a] >= nums[b]
                    by {
                        if b < ii {
                            
                        } else {
                            
                            assert(nums[a] as i64 >= min_val);
                            assert(min_val >= nums[ii] as i64);
                        }
                    }
                }
            }

            if (nums[i] as i64) < min_val {
                min_val = nums[i] as i64;
                proof {
                    min_idx = i as int;
                }
            }

            i += 1;
        }

        best as i32
    }
}

} 
