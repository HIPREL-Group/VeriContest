use vstd::prelude::*;

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

    pub fn product_except_self(nums: Vec<i32>) -> (res: Vec<i32>)
        requires 
            2 <= nums.len() <= 100_000, 
            forall |i: int| 0 <= i < nums.len() ==> -30 <= #[trigger] nums[i] <= 30, 
            forall |i: int| 0 <= i < nums.len() ==> 
                i32::MIN <= #[trigger] Self::product_of_range(nums@, 0, i) * 
                Self::product_of_range(nums@, i + 1, nums@.len() as int) <= i32::MAX,
            forall |i: int| 0 <= i <= nums.len() ==> 
                i32::MIN <= #[trigger] Self::product_of_range(nums@, 0, i) <= i32::MAX,
            forall |i: int| 0 <= i <= nums.len() ==> 
                i32::MIN <= #[trigger] Self::product_of_range(nums@, i, nums@.len() as int) <= i32::MAX,
        ensures
            res.len() == nums.len(),
            forall |i: int| 0 <= i < res.len() ==> 
                res[i] as int == Self::product_of_range(nums@, 0, i) * 
                Self::product_of_range(nums@, i + 1, nums@.len() as int)
    {
        let n = nums.len();
        
        let mut pre = Vec::with_capacity(n);
        for i in 0..n 
        {
            pre.push(nums[i]);
        }
        
        let mut suf = Vec::with_capacity(n);
        for i in 0..n 
        {
            suf.push(nums[i]);
        }

        for i in 1..n 
        {
            pre[i] = pre[i] * pre[i - 1];
            suf[n - 1 - i] = suf[n - 1 - i] * suf[n - i];
        }

        pre.insert(0, 1);
        suf.push(1);

        let mut res = Vec::with_capacity(n);
        for i in 0..n 
        {
            res.push(pre[i] * suf[i + 1]);
        }
        res
    }
}

}