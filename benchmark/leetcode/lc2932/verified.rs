use vstd::prelude::*;
use vstd::math::{max as spec_max, min as spec_min, abs as spec_abs};

fn main() {}

verus! {

pub struct Solution;

proof fn xor_comm(a: i32, b: i32)
    ensures 
        a ^ b == b ^ a, 
{
    assert(a ^ b == b ^ a) by(bit_vector);
}

proof fn xor_self_zero(a: i32)
    ensures 
        a ^ a == 0, 
{
    assert(a ^ a == 0) by(bit_vector);
}

impl Solution {
    pub fn abs(x: i32) -> (res: i32)
        requires 
            x > i32::MIN, 
        ensures 
            (res as int) == spec_abs(x as int), 
    {
        if x < 0 { -x } else { x }
    }

    pub fn max(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        if x >= y { x } else { y }
    }

    pub fn min(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_min(x as int, y as int)
    {
        if x <= y { x } else { y }
    }

    pub fn maximum_strong_pair_xor(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 50, 
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100, 
        ensures 
            forall |i: int, j: int| 
                0 <= i < nums.len() && 0 <= j < nums.len() &&
                spec_abs((nums[i] - nums[j]) as int) <= spec_min(nums[i] as int, nums[j] as int)
                ==> (nums[i] ^ nums[j]) <= res,
            exists |i: int, j: int| 
                0 <= i < nums.len() && 0 <= j < nums.len() &&
                spec_abs((nums[i] - nums[j]) as int) <= spec_min(nums[i] as int, nums[j] as int) &&
                (nums[i] ^ nums[j]) == res,
    {
        let mut max_xor = 0;
        
        proof {
            assert(0 <= spec_min(nums[0int] as int, nums[0int] as int));
            xor_self_zero(nums[0]);
        }
        
        for i in 0..nums.len() 
            invariant
                1 <= nums.len() <= 50, 
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                max_xor >= 0,
                forall |ii: int, jj: int| 
                    0 <= ii < i && 0 <= jj < nums.len() &&
                    spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int)
                    ==> (nums[ii] ^ nums[jj]) <= max_xor,
                exists |ii: int, jj: int| 
                    0 <= ii < nums.len() && 0 <= jj < nums.len() &&
                    spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int) &&
                    (nums[ii] ^ nums[jj]) == max_xor,
        {
            for j in i..nums.len() 
                invariant
                    1 <= nums.len() <= 50,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                    0 <= i < nums.len(),
                    i <= j <= nums.len(),
                    max_xor >= 0,
                    forall |ii: int, jj: int| 
                        ((0 <= ii < i && 0 <= jj < nums.len()) ||
                         (ii == i && i <= jj < j)) &&
                        spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int)
                        ==> (nums[ii] ^ nums[jj]) <= max_xor,
                    exists |ii: int, jj: int| 
                        0 <= ii < nums.len() && 0 <= jj < nums.len() &&
                        spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int) &&
                        (nums[ii] ^ nums[jj]) == max_xor,
            {
                if Self::abs(nums[i] - nums[j]) <= Self::min(nums[i], nums[j]) {
                    let current_xor = nums[i] ^ nums[j];
                    max_xor = Self::max(max_xor, current_xor);
                }
            }
            
            assert forall |ii: int, jj: int| 
                0 <= ii < i + 1 && 0 <= jj < nums.len() &&
                spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int)
                implies (nums[ii] ^ nums[jj]) <= max_xor
            by {
                if ii < i {
                    assert((0 <= ii < i && 0 <= jj < nums.len()) &&
                           spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int));
                } else {
                    if jj >= i {
                        assert((ii == i && i <= jj < nums.len()) &&
                               spec_abs((nums[ii] - nums[jj]) as int) <= spec_min(nums[ii] as int, nums[jj] as int));
                    } else {
                        xor_comm(nums[ii], nums[jj]);
                        assert((0 <= jj < i && 0 <= ii < nums.len()) &&
                               spec_abs((nums[jj] - nums[ii]) as int) <= spec_min(nums[jj] as int, nums[ii] as int));
                    }
                }
            };
        }
        
        max_xor
    }
}

}