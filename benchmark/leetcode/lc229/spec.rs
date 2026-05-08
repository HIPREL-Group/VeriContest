use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) + 
                if s.last() == value { 1 as nat } else { 0 as nat}
        }
    }

    pub fn majority_element(nums: Vec<i32>) -> (res: Vec<i32>)
        requires 
            1 <= nums.len() <= 50_000, 
            forall |i: int| 0 <= i < nums.len() 
                ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000, 
        ensures
            forall |i: int| 0 <= i < res.len() ==> Self::count_occurrences(nums@, res[i]) > nums.len() / 3,
            forall |i: int, j: int| 0 <= i < j < res.len() ==> res[i] != res[j], 
    {
        
    }
}

}