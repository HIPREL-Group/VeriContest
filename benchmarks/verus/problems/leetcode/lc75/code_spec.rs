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

    pub fn sort_colors(nums: &mut Vec<i32>)
        requires
            1 <= old(nums).len() <= 300,
            forall |i: int| 0 <= i < old(nums).len() ==> 0 <= #[trigger] old(nums)[i] <= 2,
        ensures
            nums.len() == old(nums).len(),
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
            forall |v: i32| Self::count(nums@, v) == Self::count(old(nums)@, v),
    {
        let n = nums.len();
        let mut low: usize = 0;
        let mut mid: usize = 0;
        let mut high: usize = n;

        while mid < high {
            if nums[mid] == 0 {
                let tmp_low = nums[low];
                let tmp_mid = nums[mid];
                nums.set(low, tmp_mid);
                nums.set(mid, tmp_low);
                low = low + 1;
                mid = mid + 1;
            } else if nums[mid] == 2 {
                high = high - 1;
                let tmp_mid = nums[mid];
                let tmp_high = nums[high];
                nums.set(mid, tmp_high);
                nums.set(high, tmp_mid);
            } else {
                mid = mid + 1;
            }
        }
    }
}

}

