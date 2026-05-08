use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn has_trailing_zeros(nums: Vec<i32>) -> (result: bool)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] % 2 == 0 && nums[j] % 2 == 0),
    {
        let n = nums.len();
        let mut first_even: usize = n;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                2 <= nums.len() <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                0 <= i <= n,
                first_even == n || 0 <= first_even < i,
                first_even == n ==> forall |k: int| 0 <= k < i ==> #[trigger] nums[k] % 2 != 0,
                first_even != n ==> nums[first_even as int] % 2 == 0,
                first_even != n ==> forall |k: int| 0 <= k < i && k != first_even as int ==> #[trigger] nums[k] % 2 != 0,
            decreases n - i,
        {
            if nums[i] % 2 == 0 {
                if first_even != n {
                    proof {
                        let a = first_even as int;
                        let b = i as int;
                        assert(0 <= a < nums.len());
                        assert(0 <= b < nums.len());
                        assert(a != b);
                        assert(nums[a] % 2 == 0);
                        assert(nums[b] % 2 == 0);
                        assert(exists |x: int, y: int| 0 <= x < nums.len() && 0 <= y < nums.len() && x != y && nums[x] % 2 == 0 && nums[y] % 2 == 0) by {
                            assert(0 <= a < nums.len() && 0 <= b < nums.len() && a != b && nums[a] % 2 == 0 && nums[b] % 2 == 0);
                        };
                    }
                    return true;
                }
                first_even = i;
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert forall |a: int, b: int| 0 <= a < nums.len() && 0 <= b < nums.len() && a != b implies !(nums[a] % 2 == 0 && nums[b] % 2 == 0) by {
                if first_even == n {
                    assert(nums[a] % 2 != 0);
                } else {
                    if a == first_even as int {
                        assert(nums[b] % 2 != 0);
                    } else {
                        assert(nums[a] % 2 != 0);
                    }
                }
            };
        }
        false
    }
}

}
