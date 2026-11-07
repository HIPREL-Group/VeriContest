use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_max_index(nums: Seq<i32>, idx: int) -> bool {
        0 <= idx < nums.len() &&
        forall |j: int| 0 <= j < nums.len() ==> nums[idx] >= #[trigger] nums[j]
    }

    pub open spec fn is_dominant(nums: Seq<i32>, idx: int) -> bool {
        Self::is_max_index(nums, idx) &&
        forall |j: int| 0 <= j < nums.len() && j != idx ==> nums[idx] >= 2 * #[trigger] nums[j]
    }

    pub fn dominant_index(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
            exists |i: int| #![trigger nums[i]] 0 <= i < nums.len() &&
                forall |j: int| 0 <= j < nums.len() && j != i ==> nums[i] > #[trigger] nums[j],
        ensures
            -1 <= result < nums.len() as i32,
            result >= 0 ==> Self::is_dominant(nums@, result as int),
            result < 0 ==> forall |i: int| 0 <= i < nums.len() ==> !Self::is_dominant(nums@, i),
    {
        let n = nums.len();
        let mut max_val: i32 = nums[0];
        let mut max_idx: usize = 0;
        let mut second_max: i32 = -1;
        let ghost mut sm_witness: int = -1;

        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 50,
                1 <= i <= n,
                0 <= max_idx < i,
                max_val == nums[max_idx as int],
                0 <= max_val <= 100,
                -1 <= second_max <= 100,
                second_max <= max_val,
                forall |j: int| 0 <= j < i as int ==> max_val >= #[trigger] nums[j],
                forall |j: int| 0 <= j < i as int && j != max_idx as int ==> second_max >= #[trigger] nums[j],
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100,
                i >= 2 ==> (0 <= sm_witness < i as int && sm_witness != max_idx as int && second_max == nums[sm_witness]),
                i == 1 ==> second_max == -1,
            decreases n - i,
        {
            if nums[i] > max_val {
                proof { sm_witness = max_idx as int; }
                second_max = max_val;
                max_val = nums[i];
                max_idx = i;
            } else if nums[i] > second_max {
                proof { sm_witness = i as int; }
                second_max = nums[i];
            }
            i += 1;
        }

        if max_val >= 2 * second_max {
            proof {
                assert forall |j: int| 0 <= j < nums.len() && j != max_idx as int
                    implies nums[max_idx as int] >= 2 * #[trigger] nums[j] by {
                    assert(second_max >= nums[j]);
                };
            }
            max_idx as i32
        } else {
            proof {
                assert forall |idx: int| 0 <= idx < nums.len()
                    implies !Self::is_dominant(nums@, idx) by {
                    if idx == max_idx as int {
                        assert(second_max == nums[sm_witness]);
                        assert(nums[max_idx as int] < 2 * nums[sm_witness]);
                    } else {
                        assert(max_val > nums[idx]) by {
                            let unique_max_idx = choose |mi: int| #![trigger nums[mi]] 0 <= mi < nums.len() &&
                                forall |j: int| 0 <= j < nums.len() && j != mi ==> nums[mi] > #[trigger] nums[j];
                            assert(nums[unique_max_idx] > nums[idx]);
                            assert(max_val >= nums[unique_max_idx]);
                        };
                        assert(nums[idx] < 2 * nums[max_idx as int]);
                    }
                };
            }
            -1
        }
    }
}

}
