use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_value(nums: Seq<i32>, v: int) -> bool {
        exists|i: int| 0 <= i < nums.len() && nums[i] as int == v
    }

    pub fn first_missing_positive(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() >= 1,
            nums.len() <= 100_000,
        ensures
            result >= 1,
            !Self::contains_value(nums@, result as int),
            forall|v: int| 1 <= v < result as int ==> Self::contains_value(nums@, v),
    {
        let n = nums.len();
        let mut arr = nums;
        let n_i32 = n as i32;
        let mut i: usize = 0;
        while i < n
        {
            while arr[i] >= 1 && arr[i] <= n_i32
                && arr[(arr[i] as usize) - 1] != arr[i]
            {
                let j = (arr[i] as usize) - 1;
                let vi = arr[i];
                let vj = arr[j];
                arr.set(j, vi);
                arr.set(i, vj);
            }
            i += 1;
        }
        let mut k: usize = 0;
        while k < n
        {
            if arr[k] != (k as i32) + 1 {
                return (k as i32) + 1;
            }
            k += 1;
        }
        (n as i32) + 1
    }
}

} 
