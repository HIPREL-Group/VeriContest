use vstd::prelude::*;
use vstd::math::{max as spec_max};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn product_of_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            1
        } else {
            nums[start] as int * Self::product_of_range(nums, start + 1, end)
        }
    }

    proof fn lemma_product_range_step(nums: Seq<i32>, start: int, mid: int)
        requires
            0 <= start <= mid < nums.len()
        ensures
            Self::product_of_range(nums, start, mid + 1) == 
                Self::product_of_range(nums, start, mid) * nums[mid] as int
        decreases mid - start
    {
        if start >= mid {
            assert(Self::product_of_range(nums, start, mid) == 1);
            assert(Self::product_of_range(nums, mid, mid + 1) == 
                   nums[mid] as int * Self::product_of_range(nums, mid + 1, mid + 1));
        } else {
            Self::lemma_product_range_step(nums, start + 1, mid);
            assert(Self::product_of_range(nums, start + 1, mid + 1) == 
                   Self::product_of_range(nums, start + 1, mid) * nums[mid] as int);
            assert(Self::product_of_range(nums, start, mid + 1) == Self::product_of_range(nums, start, mid) * nums[mid] as int) by {
                let a = nums[start] as int;
                let b = Self::product_of_range(nums, start + 1, mid);
                let c = nums[mid] as int;
                assert(a * (b * c) == (a * b) * c) by(nonlinear_arith)
            }
        }
    }

    pub fn max(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        if x >= y { x } else { y }
    }

    pub fn max_product(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 20_000, 
            forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10, 
            forall |i: int, j: int| 0 <= i < j <= nums.len()
                ==> i32::MIN <= #[trigger] Self::product_of_range(nums@, i, j) <= i32::MAX, 
        ensures 
            exists |i: int, j: int| 0 <= i < j <= nums.len() 
                && res == Self::product_of_range(nums@, i, j)
                && forall |k: int, l: int| 0 <= k < l <= nums.len() 
                    ==> res >= Self::product_of_range(nums@, k, l)
    {
        let n = nums.len();
        let mut ans: i32 = nums[0];
        
        proof {
            Self::lemma_product_range_step(nums@, 0, 0);
        }
        
        for i in 0..n
            invariant
                1 <= nums.len() <= 20_000, 
                forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10, 
                forall |i: int, j: int| 0 <= i < j <= nums.len()
                    ==> i32::MIN <= #[trigger] Self::product_of_range(nums@, i, j) <= i32::MAX, 
                n == nums.len(),
                forall |k: int, l: int| 0 <= k < i && k < l <= n
                    ==> ans >= Self::product_of_range(nums@, k, l),
                exists |k: int, l: int| 0 <= k < l <= n 
                    && ans == Self::product_of_range(nums@, k, l)
        {
            let mut prod: i32 = 1;
            for j in i..n
                invariant
                    1 <= nums.len() <= 20_000, 
                    forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10, 
                    forall |i: int, j: int| 0 <= i < j <= nums.len()
                        ==> i32::MIN <= #[trigger] Self::product_of_range(nums@, i, j) <= i32::MAX, 
                    n == nums.len(),
                    i <= j <= n,
                    prod == Self::product_of_range(nums@, i as int, j as int),
                    forall |k: int, l: int| 0 <= k < i && k < l <= n
                        ==> ans >= Self::product_of_range(nums@, k, l),
                    forall |l: int| i < l <= j
                        ==> ans >= Self::product_of_range(nums@, i as int, l),
                    exists |k: int, l: int| 0 <= k < l <= n 
                        && ans == Self::product_of_range(nums@, k, l)
            {
                proof {
                    Self::lemma_product_range_step(nums@, i as int, j as int);
                }
                
                prod = prod * nums[j];
                ans = Self::max(ans, prod);
            }
        }
        
        ans
    }
}

}