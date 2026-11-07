use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_array_special(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (forall |i: int| 0 <= i && i + 1 < nums.len() ==> (#[trigger] nums[i]) % 2 != nums[i + 1] % 2),
    {
        let n = nums.len();
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                1 <= i <= n,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                forall |j: int| 0 <= j && j + 1 < i as int ==> (#[trigger] nums[j]) % 2 != nums[j + 1] % 2,
            decreases n - i,
        {
            if nums[i - 1] % 2 == nums[i] % 2 {
                proof {
                    let j = i as int - 1;
                    assert(0 <= j);
                    assert(j + 1 == i as int);
                    assert(j + 1 < nums.len());
                    assert(nums[j] % 2 == nums[j + 1] % 2);
                    assert(!(forall |k: int| 0 <= k && k + 1 < nums.len() ==> (#[trigger] nums[k]) % 2 != nums[k + 1] % 2)) by {
                        if forall |k: int| 0 <= k && k + 1 < nums.len() ==> (#[trigger] nums[k]) % 2 != nums[k + 1] % 2 {
                            assert(nums[j] % 2 != nums[j + 1] % 2);
                            assert(false);
                        }
                    }
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert forall |j: int| 0 <= j && j + 1 < nums.len() implies (#[trigger] nums[j]) % 2 != nums[j + 1] % 2 by {
                assert(j + 1 < i as int);
            };
        }
        true
    }
}

}
