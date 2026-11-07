use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn binary_val(nums: Seq<i32>, len: nat) -> int
        decreases len,
    {
        if len == 0 {
            0
        } else {
            Self::binary_val(nums, (len - 1) as nat) * 2 + nums[(len - 1) as int] as int
        }
    }

    proof fn binary_val_nonneg(nums: Seq<i32>, len: nat)
        requires
            len <= nums.len(),
            forall|j: int| 0 <= j < nums.len() ==> (#[trigger] nums[j] == 0 || nums[j] == 1),
        ensures
            Self::binary_val(nums, len) >= 0,
        decreases len,
    {
        if len > 0 {
            Self::binary_val_nonneg(nums, (len - 1) as nat);
        }
    }

    proof fn mod_step_lemma(a: int, b: int)
        requires
            a >= 0,
            0 <= b <= 1,
        ensures
            ((a % 5) * 2 + b) % 5 == (a * 2 + b) % 5,
    {
        assert(((a % 5) * 2 + b) % 5 == (a * 2 + b) % 5) by(nonlinear_arith)
            requires a >= 0, 0 <= b <= 1;
    }

    pub fn prefixes_div_by5(nums: Vec<i32>) -> (result: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
        ensures
            result.len() == nums.len(),
            forall|i: int|
                0 <= i < result.len() ==> #[trigger] result[i] == (Self::binary_val(
                    nums@,
                    (i + 1) as nat,
                ) % 5 == 0),
    {
        let mut result: Vec<bool> = Vec::new();
        let mut rem: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() <= 100_000,
                result.len() == i,
                0 <= rem <= 4,
                forall|j: int|
                    0 <= j < nums.len() ==> (#[trigger] nums[j] == 0 || nums[j] == 1),
                rem as int == Self::binary_val(nums@, i as nat) % 5,
                forall|j: int|
                    0 <= j < i as int ==> #[trigger] result[j] == (Self::binary_val(
                        nums@,
                        (j + 1) as nat,
                    ) % 5 == 0),
            decreases nums.len() - i,
        {
            proof {
                Self::binary_val_nonneg(nums@, i as nat);
                Self::mod_step_lemma(
                    Self::binary_val(nums@, i as nat),
                    nums@[i as int] as int,
                );
                assert(Self::binary_val(nums@, (i + 1) as nat) == Self::binary_val(
                    nums@,
                    i as nat,
                ) * 2 + nums@[i as int] as int);
            }
            rem = (rem * 2 + nums[i]) % 5;
            result.push(rem == 0);
            i += 1;
        }
        result
    }
}

}
