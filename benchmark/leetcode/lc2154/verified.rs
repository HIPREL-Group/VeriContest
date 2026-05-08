use vstd::arithmetic::power::{lemma_pow0, lemma_pow_adds, lemma_pow1, pow};
use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub open spec fn chain_value(original: i32, k: nat) -> int {
        original as int * pow(2, k)
    }

    pub open spec fn appears(nums: Seq<i32>, v: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && #[trigger] nums[i] == v
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn find_final_value(nums: Vec<i32>, original: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            1 <= original <= 1000,
        ensures
            exists |k: nat|
                result as int == Self::chain_value(original, k)
                && forall |t: nat| t < k ==> #[trigger] Self::appears(nums@, Self::chain_value(original, t))
                && forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != result,
    {
        let mut current = original;
        let mut found = true;
        proof {
            lemma_pow0(2);
            assert(pow(2, 0) == 1);
            assert(current as int == Self::chain_value(original, 0));
            assert(exists |kk: nat| current as int == Self::chain_value(original, kk)) by {
                assert(current as int == Self::chain_value(original, 0));
            }
            assert(exists |kk: nat|
                current as int == Self::chain_value(original, kk)
                && forall |t: nat| t < kk ==> Self::appears(nums@, Self::chain_value(original, t))
            ) by {
                assert(current as int == Self::chain_value(original, 0));
            }
        }
        while found
            invariant
                1 <= nums.len() <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                original <= current,
                !found ==> forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] != current,
                exists |kk: nat|
                    current as int == Self::chain_value(original, kk)
                    && forall |t: nat| t < kk ==> #[trigger] Self::appears(nums@, Self::chain_value(original, t))
        {
            found = false;
            let mut i = 0;
            while i < nums.len()
                invariant
                    0 <= i <= nums.len(),
                    1 <= nums.len() <= 1000,
                    original <= current,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                    found <==> exists |k: int| 0 <= k < i && #[trigger] nums[k] == current
                decreases nums.len() - i
            {
                if nums[i] == current {
                    found = true;
                }
                i += 1;
            }
            if found {
                let ghost old_current = current as int;
                let ghost old_k: nat = choose |kk: nat| old_current == Self::chain_value(original, kk)
                    && forall |t: nat| t < kk ==> Self::appears(nums@, Self::chain_value(original, t));
                proof {
                    let idx = choose |k: int| 0 <= k < nums.len() && nums[k] == current;
                    assert(current == nums[idx]);
                    lemma_pow_adds(2, old_k, 1);
                    lemma_pow1(2);
                    assert(old_current == Self::chain_value(original, old_k));
                    assert(pow(2, old_k + 1) == pow(2, old_k) * pow(2, 1));
                    assert(pow(2, old_k + 1) == pow(2, old_k) * 2);
                    assert(Self::appears(nums@, Self::chain_value(original, old_k))) by {
                        assert(nums[idx] == current);
                        assert(current as int == old_current);
                        assert(old_current == Self::chain_value(original, old_k));
                    }
                }
                current *= 2;
                proof {
                    assert(current as int == old_current * 2);
                    assert(current as int == Self::chain_value(original, old_k + 1)) by(nonlinear_arith)
                        requires
                            old_current == Self::chain_value(original, old_k),
                            pow(2, old_k + 1) == pow(2, old_k) * 2,
                            current as int == old_current * 2,
                    {}
                    assert(exists |kk: nat|
                        current as int == Self::chain_value(original, kk)
                        && forall |t: nat| t < kk ==> Self::appears(nums@, Self::chain_value(original, t))
                    ) by {
                        assert(current as int == Self::chain_value(original, old_k + 1));
                        assert forall |t: nat| t < old_k + 1 implies Self::appears(nums@, Self::chain_value(original, t)) by {
                            if t < old_k {
                                assert(Self::appears(nums@, Self::chain_value(original, t)));
                            } else {
                                assert(t == old_k);
                                assert(Self::appears(nums@, Self::chain_value(original, old_k)));
                            }
                        }
                    }
                }
            }
        }
        proof {
            let ghost kk: nat = choose |k0: nat|
                current as int == Self::chain_value(original, k0)
                && forall |t: nat| t < k0 ==> Self::appears(nums@, Self::chain_value(original, t));
            assert(forall |i: int| 0 <= i < nums.len() ==> nums[i] != current);
            assert(exists |k: nat|
                current as int == Self::chain_value(original, k)
                && forall |t: nat| t < k ==> Self::appears(nums@, Self::chain_value(original, t))
                && forall |i: int| 0 <= i < nums.len() ==> nums[i] != current
            ) by {
                assert(current as int == Self::chain_value(original, kk));
            }
        }
        current
    }
}
}
