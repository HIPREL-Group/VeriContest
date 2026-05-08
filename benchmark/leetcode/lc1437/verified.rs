use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn k_length_apart(nums: Vec<i32>, k: i32) -> (result: bool)
        requires
            1 <= nums.len() <= 100000,
            0 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1,
        ensures
            result == (forall |i: int, j: int| 0 <= i < j < nums.len() && #[trigger] nums[i] == 1 && #[trigger] nums[j] == 1 ==> j - i > k),
    {
        let n = nums.len();
        let k_usize = k as usize;
        let mut i: usize = 0;
        let mut seen_one = false;
        let mut prev_one: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100000,
                0 <= k <= nums.len(),
                k_usize as int == k,
                0 <= i <= n,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1,
                !seen_one ==> forall |j: int| 0 <= j < i ==> #[trigger] nums[j] == 0,
                seen_one ==> 0 <= prev_one < i,
                seen_one ==> nums[prev_one as int] == 1,
                seen_one ==> forall |j: int| prev_one < j < i ==> #[trigger] nums[j] == 0,
                forall |a: int, b: int| 0 <= a < b < i && #[trigger] nums[a] == 1 && #[trigger] nums[b] == 1 ==> b - a > k,
            decreases n - i,
        {
            if nums[i] == 1 {
                if seen_one {
                    if i - prev_one <= k_usize {
                        proof {
                            assert(!(forall |a: int, b: int| 0 <= a < b < nums.len() && nums[a] == 1 && nums[b] == 1 ==> b - a > k)) by {
                                let a = prev_one as int;
                                let b = i as int;
                                assert(0 <= a < b < nums.len());
                                assert(nums[a] == 1);
                                assert(nums[b] == 1);
                                assert(b - a == i as int - prev_one as int);
                                assert(i as int - prev_one as int <= k_usize as int);
                                assert(k_usize as int == k);
                                assert(b - a <= k);
                            };
                        }
                        return false;
                    }
                    proof {
                        assert(i as int - prev_one as int > k_usize as int);
                        assert(k_usize as int == k);
                    }
                }
                proof {
                    assert forall |a: int, b: int| 0 <= a < b < i as int + 1 && nums[a] == 1 && nums[b] == 1 implies b - a > k by {
                        if b < i as int {
                            assert(b < i);
                        } else {
                            assert(b == i as int);
                            if seen_one {
                                assert(a <= prev_one as int) by {
                                    if a > prev_one as int {
                                        assert(prev_one < a < i);
                                        assert(nums[a] == 0);
                                        assert(false);
                                    }
                                };
                                assert(i as int - prev_one as int > k);
                                assert(b - a >= i as int - prev_one as int);
                            } else {
                                assert(nums[a] == 0);
                                assert(false);
                            }
                        }
                    };
                }
                prev_one = i;
                seen_one = true;
            } else {
                proof {
                    assert(nums[i as int] == 0);
                }
            }
            i = i + 1;
        }

        proof {
            assert(i == n);
            assert forall |a: int, b: int| 0 <= a < b < nums.len() && nums[a] == 1 && nums[b] == 1 implies b - a > k by {
                assert(b < i as int);
            };
        }
        true
    }
}

}
