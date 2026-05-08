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

    pub fn single_number(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 30_000, 
            forall |i: int| 0 <= i < nums.len() ==> -30_000 <= #[trigger] nums[i] <= 30_000, 
            exists|unique_val: i32| {
                Self::count_occurrences(nums@, unique_val) == 1 &&
                forall|other: i32| other != unique_val ==> 
                    Self::count_occurrences(nums@, other) % 2 == 0
            }
        ensures 
            Self::count_occurrences(nums@, res) == 1,
    {
        
    }
}

}