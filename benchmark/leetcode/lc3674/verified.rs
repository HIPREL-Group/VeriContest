use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_equal(nums: Seq<i32>) -> bool {
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == nums[0]
    }

    pub fn min_operations(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        ensures
            0 <= res <= 1,
            Self::all_equal(nums@) ==> res == 0,
            !Self::all_equal(nums@) ==> res == 1,
    {
        let mut i: usize = 1;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100,
                forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 100000,
                1 <= i <= nums.len(),
                forall |t: int| 1 <= t < i as int ==> #[trigger] nums@[t] == nums@[0],
            decreases nums.len() - i,
        {
            if nums[i] != nums[0] {
                proof {
                    assert(!Self::all_equal(nums@)) by {
                        if Self::all_equal(nums@) {
                            assert(0 <= i < nums.len());
                            assert(nums@[i as int] == nums@[0]);
                            assert(nums@[i as int] != nums@[0]);
                            assert(false);
                        }
                    }
                }
                return 1;
            }
            i = i + 1;
        }

        proof {
            assert(i == nums.len());
            assert(Self::all_equal(nums@)) by {
                assert forall |a: int| 0 <= a < nums.len() implies #[trigger] nums@[a] == nums@[0] by {
                    if a == 0 {
                    } else {
                        assert(1 <= a < i as int);
                        assert(nums@[a] == nums@[0]);
                    }
                }
            }
        }
        0
    }
}

}
