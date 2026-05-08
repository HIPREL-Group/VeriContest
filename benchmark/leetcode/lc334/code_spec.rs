use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn no_triplet_prefix(nums: Seq<i32>, n: int) -> bool {
        forall |a: int, b: int, c: int| #![trigger nums[a], nums[b], nums[c]]
            0 <= a < b < c < n ==> !(nums[a] < nums[b] && nums[b] < nums[c])
    }

    pub fn increasing_triplet(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 500_000,
        ensures
            res == (exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() && nums[a] < nums[b] && nums[b] < nums[c]),
    {
        let mut first: i32 = i32::MAX;
        let mut second: i32 = i32::MAX;
        let mut i: usize = 0;
        while i < nums.len() {
            let n = nums[i];
            if n <= first {
                first = n;
            } else if n <= second {
                second = n;
            } else {
                return true;
            }
            i = i + 1;
        }
        false
    }
}

}
