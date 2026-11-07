use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    pub open spec fn adjusted_val(nums: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            nums[0] as int
        } else {
            let prev = Self::adjusted_val(nums, i - 1);
            if (nums[i] as int) <= prev {
                prev + 1
            } else {
                nums[i] as int
            }
        }
    }

    
    pub open spec fn total_ops(nums: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0int
        } else {
            Self::total_ops(nums, i - 1) + (Self::adjusted_val(nums, i) - nums[i] as int)
        }
    }

    
    proof fn lemma_adjusted_val_bound(nums: Seq<i32>, i: int)
        requires
            0 <= i < nums.len(),
            forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10_000,
        ensures
            1 <= Self::adjusted_val(nums, i) <= 10_000 + i,
        decreases i,
    {
        if i <= 0 {
            assert(Self::adjusted_val(nums, 0) == nums[0] as int);
        } else {
            Self::lemma_adjusted_val_bound(nums, i - 1);
            assert(Self::adjusted_val(nums, i) == {
                let p = Self::adjusted_val(nums, i - 1);
                if (nums[i] as int) <= p { p + 1 } else { nums[i] as int }
            });
        }
    }

    
    proof fn lemma_total_ops_bound(nums: Seq<i32>, i: int)
        requires
            0 <= i < nums.len(),
            forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10_000,
        ensures
            0 <= Self::total_ops(nums, i) <= (10_000 + i) * i,
        decreases i,
    {
        if i <= 0 {
            assert(Self::total_ops(nums, 0) == 0);
        } else {
            Self::lemma_total_ops_bound(nums, i - 1);
            Self::lemma_adjusted_val_bound(nums, i);
            assert(Self::total_ops(nums, i) ==
                Self::total_ops(nums, i - 1) +
                (Self::adjusted_val(nums, i) - nums[i] as int));
            
            
            
            
            
            assert(Self::adjusted_val(nums, i) - nums[i] as int <= 10_000 + i - 1);
            assert(Self::total_ops(nums, i - 1) <= (10_000 + i - 1) * (i - 1));
            assert((10_000 + i - 1) * (i - 1) + (10_000 + i - 1) <= (10_000 + i) * i) by(nonlinear_arith)
                requires i >= 1, 0 <= 10_000 + i - 1;
        }
    }

    pub fn min_operations(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 5000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            res >= 0,
            
            forall |i: int| 0 <= i < nums.len() - 1 ==>
                #[trigger] Self::adjusted_val(nums@, i) < Self::adjusted_val(nums@, i + 1),
            
            forall |i: int| 0 <= i < nums.len() ==>
                #[trigger] Self::adjusted_val(nums@, i) >= nums[i] as int,
            
            res as int == Self::total_ops(nums@, (nums.len() - 1) as int),
    {
        let n = nums.len();
        let mut ops: i64 = 0;
        let mut prev: i64 = nums[0] as i64;
        let mut i: usize = 1;

        proof {
            assert(Self::adjusted_val(nums@, 0) == nums[0] as int);
            assert(Self::total_ops(nums@, 0) == 0);
        }

        while i < n
            invariant
                1 <= nums.len() <= 5000,
                n == nums.len(),
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10_000,
                1 <= i <= n,
                prev as int == Self::adjusted_val(nums@, (i - 1) as int),
                ops as int == Self::total_ops(nums@, (i - 1) as int),
                0 <= ops <= 75_000_000,
                1 <= prev <= 15_000,
            decreases n - i,
        {
            proof {
                
                assert(Self::adjusted_val(nums@, i as int) == {
                    let p = Self::adjusted_val(nums@, (i - 1) as int);
                    if (nums@[i as int] as int) <= p { p + 1 } else { nums@[i as int] as int }
                });
                assert(Self::total_ops(nums@, i as int) ==
                    Self::total_ops(nums@, (i - 1) as int) +
                    (Self::adjusted_val(nums@, i as int) - nums@[i as int] as int));
                
                Self::lemma_adjusted_val_bound(nums@, i as int);
                Self::lemma_total_ops_bound(nums@, i as int);
                
                assert(Self::adjusted_val(nums@, i as int) <= 10_000 + i);
                assert(i <= n - 1 <= 4999);
                
                assert((10_000 + i) * i <= 75_000_000) by(nonlinear_arith)
                    requires 1 <= i <= 4999;
            }

            if nums[i] as i64 <= prev {
                ops = ops + (prev + 1 - nums[i] as i64);
                prev = prev + 1;
            } else {
                prev = nums[i] as i64;
            }
            i += 1;
        }

        proof {
            assert forall |j: int| 0 <= j < nums@.len() - 1 implies
                #[trigger] Self::adjusted_val(nums@, j) < Self::adjusted_val(nums@, j + 1)
            by {
                assert(Self::adjusted_val(nums@, j + 1) == {
                    let p = Self::adjusted_val(nums@, j);
                    if (nums@[j + 1] as int) <= p { p + 1 } else { nums@[j + 1] as int }
                });
            }

            assert forall |j: int| 0 <= j < nums@.len() implies
                #[trigger] Self::adjusted_val(nums@, j) >= nums@[j] as int
            by {
                if j == 0 {
                    assert(Self::adjusted_val(nums@, 0) == nums@[0] as int);
                } else {
                    assert(Self::adjusted_val(nums@, j) == {
                        let p = Self::adjusted_val(nums@, j - 1);
                        if (nums@[j] as int) <= p { p + 1 } else { nums@[j] as int }
                    });
                }
            }

            Self::lemma_total_ops_bound(nums@, (nums@.len() - 1) as int);
        }

        ops as i32
    }
}

} 
