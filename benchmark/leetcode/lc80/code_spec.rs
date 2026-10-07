use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_to(s: Seq<i32>, v: i32, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else { (if s[end - 1] == v { 1int } else { 0int }) + Self::count_to(s, v, end - 1) }
    }

    pub open spec fn min_2(x: int) -> int {
        if x <= 2 { x } else { 2 }
    }

    pub fn remove_duplicates(nums: &mut Vec<i32>) -> (k: i32)
        requires
            1 <= old(nums).len() <= 30_000,
            forall |i: int| 0 <= i < old(nums).len() ==>
                -10_000 <= #[trigger] old(nums)[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < old(nums).len() ==>
                old(nums)[i] <= old(nums)[j],
        ensures
            1 <= k <= nums.len(),
            nums.len() == old(nums).len(),
            forall |i: int, j: int| 0 <= i <= j < k as int ==>
                nums[i] <= nums[j],
            forall |i: int| 0 <= i < k as int - 2 ==>
                #[trigger] nums[i] < nums[i + 2],
            forall |v: i32|
                Self::count_to(nums@, v, k as int) ==
                    Self::min_2(Self::count_to(old(nums)@, v, old(nums).len() as int)),
    {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 0;

        while fast < n {
            if slow < 2 || nums[fast] != nums[slow - 2] {
                let val = nums[fast];
                nums.set(slow, val);
                slow = slow + 1;
            }
            fast = fast + 1;
        }

        slow as i32
    }
}

}
