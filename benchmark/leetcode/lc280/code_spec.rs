use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub open spec fn is_wiggle(s: Seq<i32>) -> bool {
        forall |i: int|
            1 <= i < s.len() ==>
                if i % 2 == 1 {
                    s[i - 1] <= #[trigger] s[i]
                } else {
                    s[i - 1] >= #[trigger] s[i]
                }
    }

    pub fn wiggle_sort(nums: &mut Vec<i32>)
        requires
            1 <= old(nums).len() <= 50_000,
            forall |i: int| 0 <= i < old(nums).len() ==> 0 <= #[trigger] old(nums)[i] <= 10_000,
        ensures
            nums.len() == old(nums).len(),
            Self::is_wiggle(nums@),
            forall |v: i32| Self::count(nums@, v) == Self::count(old(nums)@, v),
    {
        let n = nums.len();
        let mut i = 1usize;
        while i < n {
            if (i % 2 == 1 && nums[i] < nums[i - 1]) || (i % 2 == 0 && nums[i] > nums[i - 1]) {
                let t = nums[i - 1];
                nums.set(i - 1, nums[i]);
                nums.set(i, t);
            }
            i += 1;
        }
    }
}

}
