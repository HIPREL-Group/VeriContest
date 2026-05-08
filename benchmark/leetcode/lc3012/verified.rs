use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_u64(a: u64, b: u64) -> u64 {
        if a <= b { a } else { b }
    }

    pub open spec fn prefix_min_u64(nums: Seq<i32>, end: int) -> u64
        decreases end,
    {
        if end <= 1 {
            nums[0] as u64
        } else {
            Self::min_u64(Self::prefix_min_u64(nums, end - 1), nums[end - 1] as u64)
        }
    }

    pub open spec fn prefix_count_eq_u64(nums: Seq<i32>, end: int, v: u64) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_count_eq_u64(nums, end - 1, v)
                + if nums[end - 1] as u64 == v { 1int } else { 0int }
        }
    }

    pub open spec fn all_divisible_u64(nums: Seq<i32>, m: u64) -> bool {
        forall |k: int| 0 <= k < nums.len() ==> (nums[k] as u64) % m == 0u64
    }

    pub open spec fn minimum_array_length_spec(nums: Seq<i32>) -> int {
        let m = Self::prefix_min_u64(nums, nums.len() as int);
        if !Self::all_divisible_u64(nums, m) {
            1
        } else {
            (Self::prefix_count_eq_u64(nums, nums.len() as int, m) + 1) / 2
        }
    }

    pub fn minimum_array_length(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result as int == Self::minimum_array_length_spec(nums@),
    {
        let n = nums.len();
        let mut min_v = nums[0] as u64;
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                1 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                min_v == Self::prefix_min_u64(nums@, i as int),
                1u64 <= min_v <= 1_000_000_000u64,
            decreases n - i,
        {
            let ghost old_i = i as int;
            let ghost old_min = min_v;
            let x = nums[i] as u64;
            if x < min_v {
                min_v = x;
            }
            proof {
                assert(Self::prefix_min_u64(nums@, old_i + 1) == Self::min_u64(Self::prefix_min_u64(nums@, old_i), nums[old_i] as u64));
                if x < old_min {
                    assert(Self::min_u64(old_min, x) == x);
                    assert(min_v == x);
                } else {
                    assert(Self::min_u64(old_min, x) == old_min);
                    assert(min_v == old_min);
                }
                assert(min_v == Self::prefix_min_u64(nums@, old_i + 1));
                assert(1u64 <= min_v <= 1_000_000_000u64);
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(min_v == Self::prefix_min_u64(nums@, n as int));
            assert(1u64 <= min_v);
        }

        i = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                min_v == Self::prefix_min_u64(nums@, n as int),
                1u64 <= min_v,
                forall |k: int| 0 <= k < i as int ==> (nums[k] as u64) % min_v == 0u64,
            decreases n - i,
        {
            let x = nums[i] as u64;
            if x % min_v != 0 {
                proof {
                    assert(!(forall |k: int| 0 <= k < nums.len() ==> (nums[k] as u64) % min_v == 0u64));
                    assert(!Self::all_divisible_u64(nums@, min_v));
                    assert(Self::minimum_array_length_spec(nums@) == 1);
                }
                return 1;
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(Self::all_divisible_u64(nums@, min_v)) by {
                assert forall |k: int| 0 <= k < nums.len() implies (nums[k] as u64) % min_v == 0u64 by {
                    assert(k < i as int);
                }
            }
        }

        let mut cnt_min: i32 = 0;
        i = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                min_v == Self::prefix_min_u64(nums@, n as int),
                Self::all_divisible_u64(nums@, min_v),
                cnt_min as int == Self::prefix_count_eq_u64(nums@, i as int, min_v),
                0 <= cnt_min as int <= i as int <= n as int,
            decreases n - i,
        {
            let ghost old_i = i as int;
            let ghost old_cnt = cnt_min as int;
            if nums[i] as u64 == min_v {
                proof {
                    assert(cnt_min as int <= n as int);
                    assert(n as int <= 100_000);
                    assert(cnt_min < 2_147_483_647);
                }
                cnt_min += 1;
            }
            proof {
                if nums[old_i] as u64 == min_v {
                    assert(cnt_min as int == old_cnt + 1);
                } else {
                    assert(cnt_min as int == old_cnt);
                }
                assert(Self::prefix_count_eq_u64(nums@, old_i + 1, min_v)
                    == Self::prefix_count_eq_u64(nums@, old_i, min_v)
                        + if nums[old_i] as u64 == min_v { 1int } else { 0int });
                assert(cnt_min as int == Self::prefix_count_eq_u64(nums@, old_i + 1, min_v));
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(cnt_min as int == Self::prefix_count_eq_u64(nums@, n as int, min_v));
            assert(min_v == Self::prefix_min_u64(nums@, nums@.len() as int));
            assert(Self::all_divisible_u64(nums@, min_v));
            assert(Self::minimum_array_length_spec(nums@)
                == (Self::prefix_count_eq_u64(nums@, nums@.len() as int, min_v) + 1) / 2);
            assert(Self::minimum_array_length_spec(nums@) == (cnt_min as int + 1) / 2);
            assert(cnt_min as int <= 100_000);
            assert((cnt_min + 1) < 2_147_483_647);
        }

        (cnt_min + 1) / 2
    }
}

}
