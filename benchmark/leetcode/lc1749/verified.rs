use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(s: Seq<i32>, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            s[k - 1] as int + Self::prefix_sum(s, k - 1)
        }
    }

    pub open spec fn subarray_sum(s: Seq<i32>, l: int, r: int) -> int {
        Self::prefix_sum(s, r + 1) - Self::prefix_sum(s, l)
    }

    proof fn prefix_sum_bound(s: Seq<i32>, k: int)
        requires
            0 <= k <= s.len(),
            forall|j: int| 0 <= j < s.len() ==> -10000 <= #[trigger] s[j] <= 10000,
        ensures
            -k * 10000 <= Self::prefix_sum(s, k) <= k * 10000,
        decreases k,
    {
        if k > 0 {
            Self::prefix_sum_bound(s, k - 1);
        }
    }

    pub fn max_absolute_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100000,
            forall|i: int| 0 <= i < nums@.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
        ensures
            result >= 0,
            forall|l: int, r: int|
                0 <= l <= r < nums@.len() ==>
                    result as int >= #[trigger] Self::subarray_sum(nums@, l, r)
                        && result as int >= -Self::subarray_sum(nums@, l, r),
            result == 0 || exists|l: int, r: int|
                0 <= l && l <= r && r < nums@.len()
                    && (result as int == Self::subarray_sum(nums@, l, r)
                        || result as int == -Self::subarray_sum(nums@, l, r)),
    {
        let n = nums.len();
        let mut s: i32 = 0;
        let mut max_prefix: i32 = 0;
        let mut min_prefix: i32 = 0;
        let ghost mut k_max: int = 0;
        let ghost mut k_min: int = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums@.len(),
                1 <= n <= 100000,
                0 <= i <= n,
                forall|j: int| 0 <= j < n as int ==> -10000 <= #[trigger] nums[j] <= 10000,
                s as int == Self::prefix_sum(nums@, i as int),
                0 <= k_max <= i as int,
                max_prefix as int == Self::prefix_sum(nums@, k_max),
                forall|k: int|
                    0 <= k <= i as int ==>
                        max_prefix as int >= #[trigger] Self::prefix_sum(nums@, k),
                0 <= k_min <= i as int,
                min_prefix as int == Self::prefix_sum(nums@, k_min),
                forall|k: int|
                    0 <= k <= i as int ==>
                        min_prefix as int <= #[trigger] Self::prefix_sum(nums@, k),
                0 <= max_prefix <= 1_000_000_000,
                -1_000_000_000 <= min_prefix <= 0,
                -1_000_000_000 <= s <= 1_000_000_000,
            decreases n - i,
        {
            proof {
                Self::prefix_sum_bound(nums@, (i + 1) as int);
                assert((i + 1) as int * 10000 <= 1_000_000_000) by(nonlinear_arith)
                    requires (i + 1) as int <= 100000;
            }
            s = s + nums[i];
            if s > max_prefix {
                max_prefix = s;
                proof { k_max = (i + 1) as int; }
            }
            if s < min_prefix {
                min_prefix = s;
                proof { k_min = (i + 1) as int; }
            }
            i = i + 1;
        }

        proof {
            assert forall|l: int, r: int|
                0 <= l <= r < nums@.len()
            implies
                (max_prefix - min_prefix) as int
                    >= #[trigger] Self::subarray_sum(nums@, l, r)
                    && (max_prefix - min_prefix) as int
                        >= -Self::subarray_sum(nums@, l, r)
            by {
                assert(max_prefix as int >= Self::prefix_sum(nums@, r + 1));
                assert(min_prefix as int <= Self::prefix_sum(nums@, l));
                assert(max_prefix as int >= Self::prefix_sum(nums@, l));
                assert(min_prefix as int <= Self::prefix_sum(nums@, r + 1));
            };

            if max_prefix - min_prefix > 0 {
                if k_max > k_min {
                    assert(0 <= k_min && k_min <= k_max - 1
                        && k_max - 1 < nums@.len() as int);
                    assert((max_prefix - min_prefix) as int
                        == Self::subarray_sum(nums@, k_min, k_max - 1));
                } else {
                    assert(0 <= k_max && k_max <= k_min - 1
                        && k_min - 1 < nums@.len() as int);
                    assert((max_prefix - min_prefix) as int
                        == -Self::subarray_sum(nums@, k_max, k_min - 1));
                }
            }
        }

        max_prefix - min_prefix
    }
}

}
