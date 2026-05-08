use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alternating_prefix(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::alternating_prefix(s, end - 1)
                + if (end - 1) % 2 == 0 {
                    s[end - 1] as int
                } else {
                    -(s[end - 1] as int)
                }
        }
    }

    pub fn alternating_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::alternating_prefix(nums@, nums.len() as int),
    {
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();
        while i < n
            invariant
                1 <= n <= 100,
                n == nums.len(),
                0 <= i <= n,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] nums[k] <= 100,
                -((i as int) * 100) <= ans as int <= (i as int) * 100,
                ans as int == Self::alternating_prefix(nums@, i as int),
            decreases n - i,
        {
            let old_i: usize = i;
            let prev: i32 = ans;
            if old_i % 2 == 0 {
                proof {
                    assert(0 <= old_i as int <= 100);
                    assert(1 <= nums[old_i as int] <= 100);
                    assert(-((old_i as int) * 100) <= prev as int <= (old_i as int) * 100);
                }
                ans = prev + nums[old_i];
                proof {
                    assert(Self::alternating_prefix(nums@, old_i as int + 1)
                        == Self::alternating_prefix(nums@, old_i as int) + nums[old_i as int] as int);
                    assert(ans as int == Self::alternating_prefix(nums@, old_i as int + 1));
                    assert(-((old_i as int + 1) * 100) <= ans as int <= (old_i as int + 1) * 100) by (nonlinear_arith)
                        requires
                            -((old_i as int) * 100) <= prev as int <= (old_i as int) * 100,
                            ans as int == prev as int + nums[old_i as int] as int,
                            1 <= nums[old_i as int] <= 100,
                    {
                    }
                }
            } else {
                proof {
                    assert(0 <= old_i as int <= 100);
                    assert(1 <= nums[old_i as int] <= 100);
                    assert(-((old_i as int) * 100) <= prev as int <= (old_i as int) * 100);
                }
                ans = prev - nums[old_i];
                proof {
                    assert(Self::alternating_prefix(nums@, old_i as int + 1)
                        == Self::alternating_prefix(nums@, old_i as int) - nums[old_i as int] as int);
                    assert(ans as int == Self::alternating_prefix(nums@, old_i as int + 1));
                    assert(-((old_i as int + 1) * 100) <= ans as int <= (old_i as int + 1) * 100) by (nonlinear_arith)
                        requires
                            -((old_i as int) * 100) <= prev as int <= (old_i as int) * 100,
                            ans as int == prev as int - nums[old_i as int] as int,
                            1 <= nums[old_i as int] <= 100,
                    {
                    }
                }
            }
            i = i + 1;
            proof {
                assert(i as int == old_i as int + 1);
                assert(ans as int == Self::alternating_prefix(nums@, i as int));
                assert(-((i as int) * 100) <= ans as int <= (i as int) * 100);
            }
        }
        proof {
            assert(i == n);
        }
        ans
    }
}

}
