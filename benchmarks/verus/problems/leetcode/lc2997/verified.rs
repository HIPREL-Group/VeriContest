use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_prefix(nums: Seq<i32>, len: int) -> i32
        recommends
            0 <= len <= nums.len(),
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            Self::xor_prefix(nums, len - 1) ^ nums[len - 1]
        }
    }

    pub open spec fn xor_all(nums: Seq<i32>) -> i32 {
        Self::xor_prefix(nums, nums.len() as int)
    }

    pub open spec fn popcount_nonneg(x: int) -> int
        decreases if x > 0 { x } else { 0int },
    {
        if x <= 0 {
            0
        } else {
            (x % 2) + Self::popcount_nonneg(x / 2)
        }
    }

    pub proof fn lemma_popcount_nonneg(x: int)
        ensures
            0 <= Self::popcount_nonneg(x),
        decreases if x > 0 { x } else { 0int },
    {
        if x <= 0 {
        } else {
            Self::lemma_popcount_nonneg(x / 2);
            assert(0 <= x % 2) by (nonlinear_arith)
                requires x > 0;
        }
    }

    pub proof fn lemma_popcount_le(x: int)
        requires
            x >= 0,
        ensures
            Self::popcount_nonneg(x) <= x,
        decreases x,
    {
        if x <= 0 {
        } else {
            Self::lemma_popcount_le(x / 2);
            assert(x % 2 <= x) by (nonlinear_arith)
                requires x > 0;
            assert(Self::popcount_nonneg(x / 2) <= x / 2);
            assert((x % 2) + Self::popcount_nonneg(x / 2) <= x) by (nonlinear_arith)
                requires
                    x > 0,
                    x % 2 <= x,
                    Self::popcount_nonneg(x / 2) <= x / 2;
        }
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            0 <= k <= 1_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            result as int == Self::popcount_nonneg((Self::xor_all(nums@) ^ k) as int),
    {
        let mut total_xor: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                total_xor == Self::xor_prefix(nums@, i as int),
            decreases nums.len() - i,
        {
            total_xor = total_xor ^ nums[i];
            i = i + 1;
        }

        let mut diff: i32 = total_xor ^ k;
        let mut answer: i32 = 0;
        let ghost target = diff as int;

        proof {
            assert((diff as int) == target);
            assert(-2_147_483_648 <= (diff as int));
            assert((diff as int) <= 2_147_483_647);
            Self::lemma_popcount_nonneg(target);
        }

        while diff > 0
            invariant
                0 <= answer,
                -2_147_483_648 <= target <= 2_147_483_647,
                answer as int + Self::popcount_nonneg(diff as int) == Self::popcount_nonneg(target),
            decreases diff,
        {
            let ghost old_answer = answer;
            let ghost old_diff = diff;

            proof {
                assert(diff as int > 0);
                assert(Self::popcount_nonneg(diff as int)
                    == (diff as int % 2) + Self::popcount_nonneg((diff / 2) as int));
                assert((diff as int % 2) == 0 || (diff as int % 2) == 1) by (nonlinear_arith)
                    requires diff as int > 0;
            }

            if diff % 2 == 1 {
                proof {
                    assert((old_diff as int % 2) == 1);
                    assert(Self::popcount_nonneg(old_diff as int)
                        == 1 + Self::popcount_nonneg((old_diff / 2) as int));
                    Self::lemma_popcount_nonneg((old_diff / 2) as int);
                    assert(1 <= Self::popcount_nonneg(old_diff as int));
                    assert(Self::popcount_nonneg(target)
                        == old_answer as int + Self::popcount_nonneg(old_diff as int));
                    assert(old_answer as int <= Self::popcount_nonneg(target) - 1);
                    if target >= 0 {
                        Self::lemma_popcount_le(target);
                        assert(Self::popcount_nonneg(target) <= target);
                        assert(target <= 2_147_483_647);
                    } else {
                        assert(Self::popcount_nonneg(target) == 0);
                    }
                    assert(Self::popcount_nonneg(target) <= 2_147_483_647);
                    assert(answer < 2_147_483_647);
                }
                answer = answer + 1;
            }
            diff = diff / 2;

            proof {
                if old_diff % 2 == 1 {
                    assert(answer == old_answer + 1);
                } else {
                    assert(answer == old_answer);
                }
                assert(answer as int == old_answer as int + (old_diff as int % 2));
                assert(old_answer as int + Self::popcount_nonneg(old_diff as int) == Self::popcount_nonneg(target));
                assert(answer as int + Self::popcount_nonneg(diff as int) == Self::popcount_nonneg(target));
            }
        }

        answer
    }
}

}
