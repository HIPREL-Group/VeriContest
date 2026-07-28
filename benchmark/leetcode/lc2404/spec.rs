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

    pub fn most_frequent_even(nums: Vec<i32>) -> (res: i32) 
        requires 
            1 <= nums.len() <= 2_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        ensures 
            ((res == -1) && (forall |i: int| 0 <= i < nums.len() ==> nums[i] % 2 == 1)) || 
            ((res % 2 == 0) && (exists |j: int| 0 <= j < nums.len() && nums[j] == res) && (forall |i: int| 0 <= i < nums.len() && nums[i] % 2 == 0
                ==> ((Self::count_occurrences(nums@, nums[i]) < Self::count_occurrences(nums@, res)) || 
                (Self::count_occurrences(nums@, nums[i]) == Self::count_occurrences(nums@, res) && res <= nums[i])))),
    {
        
    }
}

}
