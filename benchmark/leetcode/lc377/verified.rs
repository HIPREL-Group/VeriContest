use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contribution(nums: Seq<i32>, target: nat, idx: nat) -> int
        decreases target, idx,
    {
        if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
            Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat)
        } else {
            0
        }
    }

    pub open spec fn prefix_count(nums: Seq<i32>, target: nat, end: nat) -> int
        decreases target, end,
    {
        if end == 0 {
            0
        } else {
            Self::prefix_count(nums, target, (end - 1) as nat)
                + Self::contribution(nums, target, (end - 1) as nat)
        }
    }

    pub open spec fn combination_count(nums: Seq<i32>, target: nat) -> int
        decreases target,
    {
        if target == 0 {
            1
        } else {
            Self::prefix_count(nums, target, nums.len() as nat)
        }
    }

    proof fn lemma_prefix_nonneg(nums: Seq<i32>, target: nat, end: nat)
        ensures
            0 <= Self::prefix_count(nums, target, end),
        decreases target, end,
    {
        if end > 0 {
            Self::lemma_prefix_nonneg(nums, target, (end - 1) as nat);
            let idx = (end - 1) as nat;
            assert(Self::prefix_count(nums, target, end)
                == Self::prefix_count(nums, target, (end - 1) as nat)
                    + Self::contribution(nums, target, idx));
            if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
                Self::lemma_combination_nonneg(nums, ((target as int) - nums[idx as int] as int) as nat);
                assert(Self::contribution(nums, target, idx)
                    == Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat));
                assert(0 <= Self::contribution(nums, target, idx));
            } else {
                assert(Self::contribution(nums, target, idx) == 0);
            }
        }
    }

    proof fn lemma_combination_nonneg(nums: Seq<i32>, target: nat)
        ensures
            0 <= Self::combination_count(nums, target),
        decreases target,
    {
        if target > 0 {
            Self::lemma_prefix_nonneg(nums, target, nums.len() as nat);
        }
    }

    proof fn lemma_prefix_mono(nums: Seq<i32>, target: nat, small: nat, big: nat)
        requires
            small <= big <= nums.len() as nat,
        ensures
            Self::prefix_count(nums, target, small) <= Self::prefix_count(nums, target, big),
        decreases big - small,
    {
        if small < big {
            Self::lemma_prefix_mono(nums, target, small, (big - 1) as nat);
            let idx = (big - 1) as nat;
            assert(Self::prefix_count(nums, target, big)
                == Self::prefix_count(nums, target, (big - 1) as nat)
                    + Self::contribution(nums, target, idx));
            if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
                Self::lemma_combination_nonneg(nums, ((target as int) - nums[idx as int] as int) as nat);
                assert(Self::contribution(nums, target, idx)
                    == Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat));
                assert(0 <= Self::contribution(nums, target, idx));
            } else {
                assert(Self::contribution(nums, target, idx) == 0);
            }
        }
    }

    proof fn lemma_prefix_bound_total(nums: Seq<i32>, target: nat, end: nat)
        requires
            target > 0,
            end <= nums.len() as nat,
        ensures
            Self::prefix_count(nums, target, end) <= Self::combination_count(nums, target),
    {
        Self::lemma_prefix_mono(nums, target, end, nums.len() as nat);
    }

    proof fn lemma_one_step_bound(nums: Seq<i32>, target: nat, j: nat)
        requires
            j < nums.len(),
            0 < nums[j as int] as int <= target as int,
        ensures
            Self::combination_count(nums, ((target as int) - nums[j as int] as int) as nat)
                <= Self::combination_count(nums, target),
    {
        let sub = ((target as int) - nums[j as int] as int) as nat;
        assert(Self::contribution(nums, target, j) == Self::combination_count(nums, sub));
        assert(Self::prefix_count(nums, target, (j + 1) as nat)
            == Self::prefix_count(nums, target, j) + Self::contribution(nums, target, j));
        Self::lemma_prefix_nonneg(nums, target, j);
        Self::lemma_prefix_bound_total(nums, target, (j + 1) as nat);
    }

    fn combo_rec(nums: &Vec<i32>, t: usize) -> (res: i32)
        requires
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            nums.len() <= 200,
            Self::combination_count(nums@, t as nat) <= i32::MAX,
        ensures
            res as int == Self::combination_count(nums@, t as nat),
        decreases t,
    {
        if t == 0 {
            return 1;
        }
        let mut total: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                forall |p: int| 0 <= p < nums.len() ==> 1 <= #[trigger] nums[p] <= 1000,
                nums.len() <= 200,
                t > 0,
                Self::combination_count(nums@, t as nat) <= i32::MAX,
                0 <= j <= nums.len(),
                total as int == Self::prefix_count(nums@, t as nat, j as nat),
                0 <= Self::prefix_count(nums@, t as nat, j as nat) <= i32::MAX,
            decreases nums.len() - j,
        {
            let num = nums[j];
            if (num as usize) <= t {
                proof {
                    assert(0 < num as int <= t as int);
                    Self::lemma_one_step_bound(nums@, t as nat, j as nat);
                    assert(Self::combination_count(nums@, (t - num as usize) as nat)
                        <= Self::combination_count(nums@, t as nat));
                }
                let sub = Self::combo_rec(nums, t - num as usize);
                proof {
                    assert(Self::contribution(nums@, t as nat, j as nat)
                        == Self::combination_count(nums@, (t - num as usize) as nat));
                    Self::lemma_prefix_bound_total(nums@, t as nat, (j + 1) as nat);
                    assert(total as int + sub as int
                        == Self::prefix_count(nums@, t as nat, (j + 1) as nat));
                }
                total = total + sub;
            } else {
                proof {
                    assert(num as int > t as int);
                    assert(Self::contribution(nums@, t as nat, j as nat) == 0);
                    assert(Self::prefix_count(nums@, t as nat, (j + 1) as nat)
                        == Self::prefix_count(nums@, t as nat, j as nat));
                }
            }
            proof {
                let next_j = (j + 1) as nat;
                Self::lemma_prefix_nonneg(nums@, t as nat, next_j);
                Self::lemma_prefix_bound_total(nums@, t as nat, next_j);
            }
            j += 1;
        }
        proof {
            assert(j == nums.len());
            assert(total as int == Self::prefix_count(nums@, t as nat, nums.len() as nat));
            assert(total as int == Self::combination_count(nums@, t as nat));
        }
        total
    }

    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
            1 <= target <= 1000,
            Self::combination_count(nums@, target as nat) <= i32::MAX,
        ensures
            res as int == Self::combination_count(nums@, target as nat),
    {
        Self::combo_rec(&nums, target as usize)
    }
}

}
