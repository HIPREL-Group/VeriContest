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
        while j < n
            invariant
                n == nums.len(),
                2 <= j <= n,
                forall |k: int| 0 <= k < j as int - 1 ==> nums[k] <= cmax,
                exists |k: int| 0 <= k < j as int - 1 && nums[k] == cmax,
                forall |t: int| #![trigger nums[t]] 2 <= t < j as int ==>
                    forall |k: int| #![trigger nums[k]] 0 <= k < t - 1 ==> nums[k] <= nums[t],
            decreases n - j
        {
            if cmax > nums[j] {
                return false;
            }

            proof {
                assert(forall |k: int| 0 <= k < j as int - 1 ==> nums[k] <= nums[j as int]);
            }

            let prev = nums[j - 1];
            if prev > cmax {
                cmax = prev;
            }
            j += 1;
        }

        proof {
            assert(forall |t: int| #![trigger nums[t]] 2 <= t < n as int ==>
                forall |k: int| #![trigger nums[k]] 0 <= k < t - 1 ==> nums[k] <= nums[t]);
            assert(forall |i: int, j: int| #![trigger nums[i], nums[j]]
                0 <= i < j < n as int ==> nums[i] != nums[j]);
            assert(forall |i: int, j: int|
                0 <= i < j < n as int && i + 1 < j ==> nums[i] < nums[j]);
            assert(Self::no_nonlocal_inversion(nums@));
        }

        true
    }
}

}
