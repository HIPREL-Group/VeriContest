use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_path(nums: Seq<i32>, start: int, end: int, path: Seq<int>) -> bool {
        path.len() >= 1 &&
        path[0] == start &&
        path[path.len() - 1] == end &&
        forall |k: int| 
            #![trigger path[k]]
            0 <= k < path.len() ==> 
                0 <= path[k] < nums.len() &&
            (0 <= k < path.len() - 1 ==> 
                path[k + 1] > path[k] &&
                path[k + 1] <= path[k] + nums[path[k]])
    }

    pub open spec fn reachable(nums: Seq<i32>, start: int, end: int) -> bool {
        exists |path: Seq<int>| Self::is_path(nums, start, end, path)
    }

    pub fn can_jump(nums: Vec<i32>) -> (res: bool) 
        requires 
            1 <= nums.len() <= 10_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000, 
        ensures
            res == Self::reachable(nums@, 0, nums.len() - 1), 
    {
        let len = nums.len();
        let mut furthest_reachable = 0;

        for i in 0..len
        {
            if i > furthest_reachable {
                return false;
            }
            
            let new_reach = i + nums[i] as usize;
            if new_reach > furthest_reachable {
                furthest_reachable = new_reach;
            }
        }

        true
    }
}

}
