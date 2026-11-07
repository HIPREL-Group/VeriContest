use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn no_nonlocal_inversion(nums: Seq<i32>) -> bool {
        forall |i: int, j: int|
            0 <= i < j < nums.len() && i + 1 < j ==> nums[i] < nums[j]
    }

    pub fn is_ideal_permutation(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
            forall |i: int, j: int| #![trigger nums[i], nums[j]]
                0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            res <==> Self::no_nonlocal_inversion(nums@),
    {
        let n = nums.len();
        if n <= 2 {
            return true;
        }

        let mut cmax = nums[0];
        let mut j: usize = 2;
        while j < n {
            if cmax > nums[j] {
                return false;
            }
            let prev = nums[j - 1];
            if prev > cmax {
                cmax = prev;
            }
            j += 1;
        }

        true
    }
}

}
