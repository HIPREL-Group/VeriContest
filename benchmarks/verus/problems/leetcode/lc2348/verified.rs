use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(nums: Seq<i32>, i: nat, cur: nat, total: nat) -> nat
        recommends
            i <= nums.len(),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            total
        } else {
            let cur2 = if nums[i as int] == 0 { cur + 1 } else { 0 };
            let total2 = total + cur2;
            Self::scan_spec(nums, i + 1, cur2, total2)
        }
    }

    pub open spec fn zero_filled_subarray_spec(nums: Seq<i32>) -> nat {
        Self::scan_spec(nums, 0, 0, 0)
    }

    pub fn zero_filled_subarray(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            0 <= result,
            result as nat == Self::zero_filled_subarray_spec(nums@),
    {
        let mut i: usize = 0;
        let mut cur: i128 = 0;
        let mut total: i128 = 0;

        while i < nums.len()
            invariant
                1 <= nums.len() <= 100_000,
                forall |k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
                0 <= i <= nums.len(),
                0 <= cur,
                0 <= total,
                cur as nat <= i as nat,
                total as nat <= (i as nat) * (i as nat + 1) / 2,
                cur as int <= 100_000,
                total as int <= 5_000_050_000,
                Self::scan_spec(nums@, i as nat, cur as nat, total as nat) == Self::zero_filled_subarray_spec(nums@),
            decreases nums.len() - i,
        {
            let ghost old_i: nat = i as nat;
            let ghost old_cur: nat = cur as nat;
            let ghost old_total: nat = total as nat;
            let x = nums[i];

            if x == 0 {
                cur = cur + 1;
                proof {
                    assert(cur as nat == old_cur + 1);
                    assert(cur as int <= 100_000) by (nonlinear_arith)
                        requires
                            old_cur <= old_i,
                            old_i < nums.len() as nat,
                            nums.len() <= 100_000,
                            cur as nat == old_cur + 1,
                    {
                    }
                    assert(total + cur < i128::MAX) by (nonlinear_arith)
                        requires
                            total as int <= 5_000_050_000,
                            cur as int <= 100_000,
                    {
                    }
                }
                total = total + cur;

                proof {
                    assert(cur as nat == old_cur + 1);
                    assert(total as nat == old_total + cur as nat);
                    assert(Self::scan_spec(nums@, old_i, old_cur, old_total)
                        == Self::scan_spec(nums@, old_i + 1, cur as nat, total as nat));
                    assert(cur as nat <= old_i + 1);
                    assert(total as nat <= (old_i + 1) * (old_i + 2) / 2) by (nonlinear_arith)
                        requires
                            old_total <= old_i * (old_i + 1) / 2,
                            old_cur <= old_i,
                            total as nat == old_total + cur as nat,
                            cur as nat == old_cur + 1,
                    {
                    }
                    assert(total as int <= 5_000_050_000) by (nonlinear_arith)
                        requires
                            total as nat <= (old_i + 1) * (old_i + 2) / 2,
                            old_i < nums.len() as nat,
                            nums.len() <= 100_000,
                    {
                    }
                }
            } else {
                cur = 0;
                proof {
                    assert(total as nat == old_total);
                    assert(Self::scan_spec(nums@, old_i, old_cur, old_total)
                        == Self::scan_spec(nums@, old_i + 1, cur as nat, total as nat));
                    assert(cur as nat <= old_i + 1);
                    assert(total as nat <= (old_i + 1) * (old_i + 2) / 2) by (nonlinear_arith)
                        requires
                            old_total <= old_i * (old_i + 1) / 2,
                            total as nat == old_total,
                    {
                    }
                    assert(total as int <= 5_000_050_000) by (nonlinear_arith)
                        requires
                            total as nat <= (old_i + 1) * (old_i + 2) / 2,
                            old_i < nums.len() as nat,
                            nums.len() <= 100_000,
                    {
                    }
                }
            }

            i = i + 1;

            proof {
                assert(i as nat == old_i + 1);
                assert(Self::scan_spec(nums@, i as nat, cur as nat, total as nat)
                    == Self::zero_filled_subarray_spec(nums@)) by {
                    assert(Self::scan_spec(nums@, old_i, old_cur, old_total)
                        == Self::zero_filled_subarray_spec(nums@));
                }
            }
        }

        proof {
            assert(i == nums.len());
            assert(Self::scan_spec(nums@, nums.len() as nat, cur as nat, total as nat) == total as nat);
            assert(total as nat == Self::zero_filled_subarray_spec(nums@));
            assert(total as nat <= (nums.len() as nat) * (nums.len() as nat + 1) / 2);
            assert((nums.len() as nat) * (nums.len() as nat + 1) / 2 <= 5_000_050_000nat) by (nonlinear_arith)
                requires
                    nums.len() <= 100_000,
            {
            }
            assert(total <= i64::MAX as i128);
        }

        total as i64
    }
}

}
