use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_prefix(nums: Seq<i32>, len: int) -> bool
        decreases len,
    {
        if len <= 0 {
            true
        } else if len == 1 {
            false
        } else {
            let two_equal = nums[len - 2] == nums[len - 1] && Self::valid_prefix(nums, len - 2);
            let three_equal = len >= 3
                && nums[len - 3] == nums[len - 2]
                && nums[len - 2] == nums[len - 1]
                && Self::valid_prefix(nums, len - 3);
            let three_inc = len >= 3
                && nums[len - 3] + 1 == nums[len - 2]
                && nums[len - 2] + 1 == nums[len - 1]
                && Self::valid_prefix(nums, len - 3);
            two_equal || three_equal || three_inc
        }
    }

    pub fn valid_partition(nums: Vec<i32>) -> (ans: bool)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
        ensures
            ans == Self::valid_prefix(nums@, nums.len() as int),
    {
        let n = nums.len() as i32;
        let mut dp: Vec<i32> = Vec::new();
        dp.push(1);
        let mut i: i32 = 1;
        while i <= n
            invariant
                1 <= i <= n + 1,
                n == nums.len() as i32,
                2 <= n <= 100000,
                dp.len() == i as usize,
                forall |j: int| 0 <= j < i ==> dp[j] == (if Self::valid_prefix(nums@, j) { 1i32 } else { 0i32 }),
                forall |j: int| 0 <= j < i ==> 0 <= #[trigger] dp[j] <= 1,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000,
            decreases n + 1 - i,
        {
            let mut cur: i32 = 0;
            if i >= 2 {
                if nums[(i - 2) as usize] == nums[(i - 1) as usize] && dp[(i - 2) as usize] == 1 {
                    cur = 1;
                }
            }
            if i >= 3 {
                if nums[(i - 3) as usize] == nums[(i - 2) as usize] && nums[(i - 2) as usize] == nums[(i - 1) as usize] && dp[(i - 3) as usize] == 1 {
                    cur = 1;
                }
                if nums[(i - 3) as usize] + 1 == nums[(i - 2) as usize] && nums[(i - 2) as usize] + 1 == nums[(i - 1) as usize] && dp[(i - 3) as usize] == 1 {
                    cur = 1;
                }
            }
            proof {
                if i >= 2 {
                    assert(dp[(i - 2) as int] == (if Self::valid_prefix(nums@, (i - 2) as int) { 1i32 } else { 0i32 }));
                }
                if i >= 3 {
                    assert(dp[(i - 3) as int] == (if Self::valid_prefix(nums@, (i - 3) as int) { 1i32 } else { 0i32 }));
                }

                if i >= 2 {
                    let two_eq = nums@[(i - 2) as int] == nums@[(i - 1) as int] && dp[(i - 2) as int] == 1;
                    let three_eq = i >= 3
                        && nums@[(i - 3) as int] == nums@[(i - 2) as int]
                        && nums@[(i - 2) as int] == nums@[(i - 1) as int]
                        && dp[(i - 3) as int] == 1;
                    let three_inc = i >= 3
                        && nums@[(i - 3) as int] + 1 == nums@[(i - 2) as int]
                        && nums@[(i - 2) as int] + 1 == nums@[(i - 1) as int]
                        && dp[(i - 3) as int] == 1;

                    assert(cur == 1 <==> (two_eq || three_eq || three_inc));

                    if two_eq {
                        assert(Self::valid_prefix(nums@, (i - 2) as int));
                    }
                    if three_eq || three_inc {
                        assert(Self::valid_prefix(nums@, (i - 3) as int));
                    }

                    assert(two_eq ==> (nums@[(i - 2) as int] == nums@[(i - 1) as int] && Self::valid_prefix(nums@, (i - 2) as int)));
                    assert(three_eq ==> (nums@[(i - 3) as int] == nums@[(i - 2) as int]
                        && nums@[(i - 2) as int] == nums@[(i - 1) as int]
                        && Self::valid_prefix(nums@, (i - 3) as int)));
                    assert(three_inc ==> (nums@[(i - 3) as int] + 1 == nums@[(i - 2) as int]
                        && nums@[(i - 2) as int] + 1 == nums@[(i - 1) as int]
                        && Self::valid_prefix(nums@, (i - 3) as int)));

                    assert(Self::valid_prefix(nums@, i as int) <==> (two_eq || three_eq || three_inc));
                    assert(cur == (if Self::valid_prefix(nums@, i as int) { 1i32 } else { 0i32 }));
                }
                if i == 1 {
                    assert(!Self::valid_prefix(nums@, i as int));
                    assert(cur == 0i32);
                }
                assert(i + 1 <= 100001) by (nonlinear_arith)
                    requires
                        i <= n,
                        n <= 100000;
            }
            dp.push(cur);
            i = i + 1;
        }
        dp[n as usize] == 1
    }
}

}
