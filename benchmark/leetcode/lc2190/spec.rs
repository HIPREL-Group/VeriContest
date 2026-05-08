use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_following(nums: Seq<i32>, key: i32, target: i32, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 1 {
            0
        } else {
            Self::count_following(nums, key, target, end - 1)
                + if nums[end - 2] == key && nums[end - 1] == target { 1int } else { 0int }
        }
    }

    pub open spec fn all_followers_leq_target(nums: Seq<i32>, key: i32, n: int, target: int) -> bool {
        Self::count_following(nums, key, key, n) <= Self::count_following(nums, key, target as i32, n)
            && (forall |t: int| 1 <= t <= 1000 ==>
                #[trigger] Self::count_following(nums, key, t as i32, n)
                    <= Self::count_following(nums, key, target as i32, n))
    }

    pub fn most_frequent(nums: Vec<i32>, key: i32) -> (result: i32)
        requires
            2 <= nums.len() <= 1000,
            1 <= key <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            exists |i: int| 0 <= i < nums.len() - 1 && nums[i] == key,
            forall |t1: int, t2: int|
                1 <= t1 <= 1000 && 1 <= t2 <= 1000
                    && #[trigger] Self::all_followers_leq_target(nums@, key, nums.len() as int, t1)
                    && #[trigger] Self::all_followers_leq_target(nums@, key, nums.len() as int, t2)
                    ==> t1 == t2,
        ensures
            1 <= result <= 1000,
            forall |t: int| 1 <= t <= 1000 ==> #[trigger] Self::count_following(nums@, key, t as i32, nums.len() as int)
                <= Self::count_following(nums@, key, result, nums.len() as int),
    {
    }
}

}
