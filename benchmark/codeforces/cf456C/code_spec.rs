use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn freq_prefix(nums: Seq<i32>, v: int, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::freq_prefix(nums, v, end - 1) + if (nums[end - 1] as int) == v {
                1int
            } else {
                0int
            }
        }
    }

    pub open spec fn freq_at(nums: Seq<i32>, v: int) -> int {
        Self::freq_prefix(nums, v, nums.len() as int)
    }

    pub open spec fn canonical_counts(nums: Seq<i32>) -> Seq<u64> {
        Seq::new(100_001, |i: int|
            if i == 0 {
                0u64
            } else {
                Self::freq_at(nums, i) as u64
            }
        )
    }

    pub open spec fn dp_best(cnt: Seq<u64>, i: int) -> int
        recommends
            0 <= i <= 100_000,
            cnt.len() == 100_001,
            forall |k: int| 0 <= k < cnt.len() ==> #[trigger] cnt[k] <= 100_000,
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            let prev2 = if i >= 2 {
                Self::dp_best(cnt, i - 2)
            } else {
                0
            };
            let take = prev2 + i * (cnt[i] as int);
            let skip = Self::dp_best(cnt, i - 1);
            if take > skip {
                take
            } else {
                skip
            }
        }
    }

    pub fn max_boredom_points(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
        ensures
            result as int == Self::dp_best(Self::canonical_counts(nums@), 100_000),
    {
        let mut cnt: Vec<u64> = Vec::new();
        let mut t: usize = 0;
        while t < 100_001 {
            cnt.push(0);
            t = t + 1;
        }
        let mut j: usize = 0;
        while j < nums.len() {
            let v = nums[j] as usize;
            let oldc = cnt[v];
            cnt.set(v, oldc + 1);
            j = j + 1;
        }
        let mut dp_i_minus_2: i64 = 0;
        let mut dp_i_minus_1: i64 = 0;
        let mut i_val: usize = 1;
        while i_val <= 100_000 {
            let vi = i_val as i64;
            let take = dp_i_minus_2 + vi * (cnt[i_val] as i64);
            let cur = if take > dp_i_minus_1 {
                take
            } else {
                dp_i_minus_1
            };
            dp_i_minus_2 = dp_i_minus_1;
            dp_i_minus_1 = cur;
            i_val = i_val + 1;
        }
        dp_i_minus_1
    }
}

}
