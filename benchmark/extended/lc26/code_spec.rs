use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn remove_duplicates(nums: &mut Vec<i32>) -> (k: i32)
        requires
            1 <= old(nums).len() <= 30_000,
            forall |i: int| 0 <= i < old(nums).len() ==>
                -100 <= #[trigger] old(nums)[i] <= 100,
            forall |i: int, j: int| 0 <= i <= j < old(nums).len() ==>
                old(nums)[i] <= old(nums)[j],
        ensures
            1 <= k <= nums.len(),
            nums.len() == old(nums).len(),
            forall |i: int, j: int| 0 <= i < j < k as int ==> nums[i] < nums[j],
            forall |i: int| 0 <= i < old(nums).len() ==>
                exists |j: int| 0 <= j < k as int && nums[j] == #[trigger] old(nums)[i],
    {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 1;

        while fast < n {
            if nums[fast] != nums[slow] {
                let val = nums[fast];
                slow = slow + 1;
                nums.set(slow, val);
            }
            fast = fast + 1;
        }

        (slow as i32) + 1
    }
}

}
