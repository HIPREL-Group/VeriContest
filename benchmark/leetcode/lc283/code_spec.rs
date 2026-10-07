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

    pub open spec fn nonzero_seq_range(s: Seq<i32>, start: int, end: int) -> Seq<i32>
        decreases end - start when start <= end
    {
        if start >= end {
            Seq::empty()
        } else {
            let rest = Self::nonzero_seq_range(s, start + 1, end);
            if s[start] != 0 { seq![s[start]] + rest } else { rest }
        }
    }

    pub open spec fn nonzero_seq(s: Seq<i32>) -> Seq<i32> {
        Self::nonzero_seq_range(s, 0, s.len() as int)
    }

    pub fn move_zeroes(nums: &mut Vec<i32>)
        requires
            1 <= (*old(nums)).len() <= 10_000,
            forall |i: int| 0 <= i < (*old(nums)).len() ==>
                i32::MIN <= #[trigger] (*old(nums))[i] <= i32::MAX,
        ensures
            nums.len() == old(nums).len(),
            forall |i: int, j: int|
                0 <= i < j < nums.len() && nums[j] != 0 ==> nums[i] != 0,
            forall |i: int|
                0 <= i < nums.len() && nums[i] == 0 ==>
                forall |j: int| i < j < nums.len() ==> nums[j] == 0,
            forall |v: i32| Self::count(nums@, v) == Self::count(old(nums)@, v),
            Self::nonzero_seq(nums@) == Self::nonzero_seq(old(nums)@),
    {
        let mut left = 0;
        let n = nums.len();

        for right in 0..n
        {
            if nums[right] != 0 {
                let temp = nums[left];
                nums[left] = nums[right];
                nums[right] = temp;
                left += 1;
            }
        }
    }
}

}
