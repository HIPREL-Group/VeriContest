use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn repeat_val(val: i32, count: int) -> Seq<i32>
        decreases count,
    {
        if count <= 0 {
            seq![]
        } else {
            Self::repeat_val(val, count - 1).push(val)
        }
    }

    pub open spec fn decompress_spec(nums: Seq<i32>, pair_idx: int) -> Seq<i32>
        decreases nums.len() - 2 * pair_idx,
    {
        if pair_idx >= nums.len() / 2 {
            seq![]
        } else {
            Self::repeat_val(nums[2 * pair_idx + 1], nums[2 * pair_idx] as int)
                + Self::decompress_spec(nums, pair_idx + 1)
        }
    }

    proof fn lemma_repeat_val_len(val: i32, count: int)
        requires
            count >= 0,
        ensures
            Self::repeat_val(val, count).len() == count,
        decreases count,
    {
        if count > 0 {
            Self::lemma_repeat_val_len(val, count - 1);
        }
    }

    pub fn decompress_rl_elist(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 100,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result@ == Self::decompress_spec(nums@, 0),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                nums.len() % 2 == 0,
                2 <= nums.len() <= 100,
                i <= nums.len(),
                i % 2 == 0,
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                Self::decompress_spec(nums@, 0) =~= result@ + Self::decompress_spec(
                    nums@,
                    (i / 2) as int,
                ),
            decreases nums.len() - i,
        {
            let freq = nums[i];
            let val = nums[i + 1];
            let ghost pair_idx = (i / 2) as int;
            let ghost old_result = result@;
            let mut j: i32 = 0;
            while j < freq
                invariant
                    nums.len() % 2 == 0,
                    2 <= nums.len() <= 100,
                    i < nums.len(),
                    i % 2 == 0,
                    forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                    freq == nums[i as int],
                    val == nums[i as int + 1],
                    1 <= freq <= 100,
                    1 <= val <= 100,
                    0 <= j <= freq,
                    pair_idx == (i / 2) as int,
                    old_result == result@.take(old_result.len() as int),
                    result@ =~= old_result + Self::repeat_val(val, j as int),
                decreases freq - j,
            {
                proof {
                    Self::lemma_repeat_val_len(val, j as int);
                    assert(result@.push(val) =~= old_result + Self::repeat_val(val, j as int)
                        + seq![val]);
                    assert(Self::repeat_val(val, j as int).push(val) =~= Self::repeat_val(
                        val,
                        j + 1,
                    ));
                    assert(old_result + Self::repeat_val(val, j as int) + seq![val] =~= old_result
                        + Self::repeat_val(val, (j + 1) as int));
                }
                result.push(val);
                j = j + 1;
            }
            proof {
                assert(result@ =~= old_result + Self::repeat_val(val, freq as int));
                assert(Self::decompress_spec(nums@, pair_idx) =~= Self::repeat_val(
                    nums@[2 * pair_idx + 1],
                    nums@[2 * pair_idx] as int,
                ) + Self::decompress_spec(nums@, pair_idx + 1));
                assert(Self::decompress_spec(nums@, 0) =~= old_result + Self::decompress_spec(
                    nums@,
                    pair_idx,
                ));
                assert(Self::decompress_spec(nums@, 0) =~= old_result + Self::repeat_val(
                    val,
                    freq as int,
                ) + Self::decompress_spec(nums@, pair_idx + 1));
                assert(result@ + Self::decompress_spec(nums@, pair_idx + 1) =~= old_result
                    + Self::repeat_val(val, freq as int) + Self::decompress_spec(
                    nums@,
                    pair_idx + 1,
                ));
                assert(Self::decompress_spec(nums@, 0) =~= result@ + Self::decompress_spec(
                    nums@,
                    pair_idx + 1,
                ));
            }
            i = i + 2;
        }
        proof {
            assert(Self::decompress_spec(nums@, (i / 2) as int) =~= seq![]);
            assert(result@ + seq![] =~= result@);
        }
        result
    }
}

} 
