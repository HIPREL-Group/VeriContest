use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min_patches_from(nums: Seq<i32>, n: nat, i: nat, miss: nat) -> nat
        recommends
            i <= nums.len(),
            1 <= miss,
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10000,
            forall|a: int, b: int| 0 <= a < b < nums.len() ==> nums[a] <= nums[b],
        decreases nums.len() - i, if miss > n { 0nat } else { (n - miss + 1nat) as nat },
    {
        if miss > n {
            0nat
        } else if i < nums.len() && nums[i as int] as nat <= miss {
            let miss2 = miss + nums[i as int] as nat;
            if miss2 > n {
                0nat
            } else {
                Self::spec_min_patches_from(nums, n, i + 1, miss2)
            }
        } else {
            let miss2 = miss + miss;
            if miss2 > n {
                1nat
            } else if miss2 <= miss {
                1nat
            } else {
                1nat + Self::spec_min_patches_from(nums, n, i, miss2)
            }
        }
    }

    pub open spec fn spec_min_patches(nums: Seq<i32>, n: int) -> nat
        recommends
            1 <= n,
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10000,
            forall|a: int, b: int| 0 <= a < b < nums.len() ==> nums[a] <= nums[b],
    {
        Self::spec_min_patches_from(nums, n as nat, 0nat, 1nat)
    }

    pub fn min_patches(nums: Vec<i32>, n: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            1 <= n <= 2147483647,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
            forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
        ensures
            0 <= res,
            res as nat == Self::spec_min_patches(nums@, n as int),
    {
        let mut miss: i64 = 1;
        let mut patches: i64 = 0;
        let mut i: usize = 0;
        let target = n as i64;

        while miss <= target {
            if i < nums.len() && (nums[i] as i64) <= miss {
                miss += nums[i] as i64;
                i += 1;
            } else {
                miss += miss;
                patches += 1;
            }
        }

        patches as i32
    }
}

}
