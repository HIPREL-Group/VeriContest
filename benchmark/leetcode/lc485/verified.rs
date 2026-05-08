use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(nums: Seq<i32>, i: nat, cur: nat, best: nat) -> nat
        recommends
            i <= nums.len(),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            best
        } else {
            let cur2 = if nums[i as int] == 1 { cur + 1 } else { 0 };
            let best2 = if best < cur2 { cur2 } else { best };
            Self::scan_spec(nums, i + 1, cur2, best2)
        }
    }

    pub open spec fn find_max_consecutive_ones_spec(nums: Seq<i32>) -> nat {
        Self::scan_spec(nums, 0, 0, 0)
    }

    pub fn find_max_consecutive_ones(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] == 0 || nums[i] == 1,
        ensures
            0 <= res,
            res as nat == Self::find_max_consecutive_ones_spec(nums@),
    {
        let mut i: usize = 0;
        let mut cur: i32 = 0;
        let mut best: i32 = 0;

        while i < nums.len()
            invariant
                1 <= nums.len() <= 100_000,
                forall|k: int| 0 <= k < nums.len() ==> nums[k] == 0 || nums[k] == 1,
                0 <= i <= nums.len(),
                0 <= cur,
                0 <= best,
                cur as nat <= i as nat,
                Self::scan_spec(nums@, i as nat, cur as nat, best as nat)
                    == Self::find_max_consecutive_ones_spec(nums@),
            decreases nums.len() - i,
        {
            let ghost old_i_nat: nat = i as nat;
            let ghost old_cur_nat: nat = cur as nat;
            let ghost old_best_nat: nat = best as nat;
            let ghost old_i_int: int = i as int;

            let x = nums[i];

            proof {
                assert(old_i_nat < nums@.len());
                assert(x == nums@[old_i_int]);
            }

            if x == 1 {
                proof {
                    assert(cur < i32::MAX) by (nonlinear_arith)
                        requires
                            cur as nat <= i as nat,
                            i < nums.len(),
                            nums.len() <= 100_000,
                    {
                    }
                }
                cur = cur + 1;
                if best < cur {
                    best = cur;
                }

                proof {
                    assert(cur as nat == old_cur_nat + 1);
                    assert(best as nat == if old_best_nat < cur as nat {
                        cur as nat
                    } else {
                        old_best_nat
                    });

                    assert(Self::scan_spec(nums@, old_i_nat, old_cur_nat, old_best_nat)
                        == Self::scan_spec(nums@, old_i_nat + 1, cur as nat, best as nat));
                }
            } else {
                cur = 0;

                proof {
                    assert(best as nat == old_best_nat);
                    assert(Self::scan_spec(nums@, old_i_nat, old_cur_nat, old_best_nat)
                        == Self::scan_spec(nums@, old_i_nat + 1, cur as nat, best as nat));
                }
            }

            i = i + 1;

            proof {
                assert(i as nat == old_i_nat + 1);
                assert(Self::scan_spec(nums@, i as nat, cur as nat, best as nat)
                    == Self::find_max_consecutive_ones_spec(nums@)) by {
                    assert(Self::scan_spec(nums@, old_i_nat, old_cur_nat, old_best_nat)
                        == Self::find_max_consecutive_ones_spec(nums@));
                }

                if x == 1 {
                    assert(cur as nat <= i as nat) by (nonlinear_arith)
                        requires
                            cur as nat == old_cur_nat + 1,
                            old_cur_nat <= old_i_nat,
                            i as nat == old_i_nat + 1,
                    {
                    }
                } else {
                    assert(cur as nat <= i as nat);
                }
            }
        }

        proof {
            assert(i == nums.len());
            assert(Self::scan_spec(nums@, nums.len() as nat, cur as nat, best as nat) == best as nat);
            assert(best as nat == Self::find_max_consecutive_ones_spec(nums@));
        }

        best
    }
}

} 
