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

    #[verifier::exec_allows_no_decreases_clause]
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

        while miss <= target
            invariant
                1 <= nums.len() <= 1000,
                1 <= n <= 2147483647,
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10000,
                forall|a: int, b: int| 0 <= a < b < nums.len() ==> nums[a] <= nums[b],
                target == n as i64,
                0 <= i <= nums.len(),
                1 <= miss,
                0 <= patches <= target,
                patches + 1 <= miss,
                patches as nat + Self::spec_min_patches_from(nums@, n as nat, i as nat, miss as nat)
                    == Self::spec_min_patches(nums@, n as int),
        {
            if i < nums.len() && (nums[i] as i64) <= miss {
                proof {
                    let ii = i as int;
                    assert(0 <= ii < nums.len());
                    assert(1 <= nums[ii] <= 10000);
                    assert((nums[ii] as i64) <= miss);
                    assert(miss <= 2147483647) by (nonlinear_arith)
                        requires
                            miss <= target,
                            target == n as i64,
                            n <= 2147483647,
                    {
                    }
                    assert(miss + nums[ii] as i64 <= 2147493647) by (nonlinear_arith)
                        requires
                            miss <= 2147483647,
                            nums[ii] <= 10000,
                    {
                    }
                    assert(Self::spec_min_patches_from(nums@, n as nat, i as nat, miss as nat)
                        == Self::spec_min_patches_from(nums@, n as nat, i as nat + 1nat, miss as nat + nums[ii] as nat));
                }
                miss += nums[i] as i64;
                i += 1;
            } else {
                proof {
                    assert(patches < target) by (nonlinear_arith)
                        requires
                            patches + 1 <= miss,
                            miss <= target,
                    {
                    }
                    assert(miss + miss <= 9223372036854775807) by (nonlinear_arith)
                        requires
                            1 <= miss,
                            miss <= target,
                            target == n as i64,
                            n <= 2147483647,
                    {
                    }
                    assert(Self::spec_min_patches_from(nums@, n as nat, i as nat, miss as nat)
                        == 1nat + Self::spec_min_patches_from(nums@, n as nat, i as nat, miss as nat + miss as nat));
                }
                miss += miss;
                patches += 1;
                proof {
                    assert(patches + 1 <= miss) by (nonlinear_arith)
                        requires
                            ((patches - 1) + 1) <= miss / 2,
                            1 <= miss / 2,
                            miss == 2 * (miss / 2),
                    {
                    }
                    assert(patches <= target) by (nonlinear_arith)
                        requires
                            patches - 1 < target,
                    {
                    }
                }
            }
        }

        proof {
            assert(miss > target);
            assert(miss as int > n as int);
            assert(Self::spec_min_patches_from(nums@, n as nat, i as nat, miss as nat) == 0nat);
            assert(patches as nat == Self::spec_min_patches(nums@, n as int));
            assert(target <= 2147483647);
            assert(patches <= 2147483647) by (nonlinear_arith)
                requires
                    patches <= target,
                    target <= 2147483647,
            {
            }
        }

        patches as i32
    }
}

}
