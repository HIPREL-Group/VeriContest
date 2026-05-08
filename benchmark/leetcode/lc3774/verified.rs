use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value_prefix(nums: Seq<i32>, end: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value_prefix(nums, end - 1, v)
                + if nums[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn count_value(nums: Seq<i32>, v: int) -> int {
        Self::count_value_prefix(nums, nums.len() as int, v)
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sum_smallest_from(nums: Seq<i32>, k: int, v: int) -> int
        decreases 101 - v,
    {
        if k <= 0 || v > 100 {
            0
        } else {
            let c = Self::count_value(nums, v);
            let t = Self::min_int(k, c);
            t * v + Self::sum_smallest_from(nums, k - t, v + 1)
        }
    }

    pub open spec fn sum_largest_from(nums: Seq<i32>, k: int, v: int) -> int
        decreases v,
    {
        if k <= 0 || v < 1 {
            0
        } else {
            let c = Self::count_value(nums, v);
            let t = Self::min_int(k, c);
            t * v + Self::sum_largest_from(nums, k - t, v - 1)
        }
    }

    pub open spec fn sum_smallest_k(nums: Seq<i32>, k: int) -> int {
        Self::sum_smallest_from(nums, k, 1)
    }

    pub open spec fn sum_largest_k(nums: Seq<i32>, k: int) -> int {
        Self::sum_largest_from(nums, k, 100)
    }

    pub open spec fn abs_int(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    proof fn lemma_count_value_prefix_step(nums: Seq<i32>, end: int, v: int)
        requires
            0 <= end < nums.len(),
        ensures
            Self::count_value_prefix(nums, end + 1, v)
                == Self::count_value_prefix(nums, end, v)
                    + if nums[end] as int == v { 1int } else { 0int },
    {
    }

    pub fn abs_difference(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= nums.len(),
        ensures
            res as int == Self::abs_int(Self::sum_largest_k(nums@, k as int) - Self::sum_smallest_k(nums@, k as int)),
    {
        let n = nums.len();
        let mut freq: Vec<i64> = vec![0; 101];
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                0 <= i <= n,
                freq.len() == 101,
                forall |x: int| 0 <= x < 101 ==> 0 <= #[trigger] freq[x] <= i,
                forall |v: int| 1 <= v <= 100 ==> #[trigger] freq[v] as int == Self::count_value_prefix(nums@, i as int, v),
            decreases n - i,
        {
            let idx = nums[i] as usize;
            let ghost old_freq = freq@;
            proof {
                assert(1 <= nums[i as int] <= 100);
                assert(1 <= idx <= 100);
                assert(idx < freq.len());
                Self::lemma_count_value_prefix_step(nums@, i as int, idx as int);
                assert(freq[idx as int] <= i as int);
                assert(freq[idx as int] + 1 <= i as int + 1);
            }
            freq.set(idx, freq[idx] + 1);
            proof {
                assert forall |x: int| 0 <= x < 101 implies 0 <= #[trigger] freq[x] <= i + 1 by {
                    if x == idx as int {
                        assert(freq[x] == old_freq[x] + 1);
                        assert(old_freq[x] <= i);
                    } else {
                        assert(freq[x] == old_freq[x]);
                        assert(old_freq[x] <= i);
                    }
                };
                assert forall |v: int| 1 <= v <= 100 implies #[trigger] freq[v] as int == Self::count_value_prefix(nums@, i as int + 1, v) by {
                    if v == idx as int {
                        assert(old_freq[v] as int == Self::count_value_prefix(nums@, i as int, v));
                        Self::lemma_count_value_prefix_step(nums@, i as int, v);
                        assert(nums@[i as int] == v as i32);
                        assert(freq[v] == old_freq[v] + 1);
                    } else {
                        assert(freq[v] == old_freq[v]);
                        assert(old_freq[v] as int == Self::count_value_prefix(nums@, i as int, v));
                        Self::lemma_count_value_prefix_step(nums@, i as int, v);
                        assert(nums@[i as int] != v as i32);
                    }
                };
            }
            i = i + 1;
        }

        proof {
            assert(i == n);
            assert forall |v: int| 1 <= v <= 100 implies #[trigger] freq[v] as int == Self::count_value(nums@, v) by {
                assert(freq[v] as int == Self::count_value_prefix(nums@, n as int, v));
                assert(Self::count_value(nums@, v) == Self::count_value_prefix(nums@, nums.len() as int, v));
                assert(nums.len() == n);
            };
        }

        let ghost total_small = Self::sum_smallest_k(nums@, k as int);
        let ghost total_large = Self::sum_largest_k(nums@, k as int);

        let mut remaining_small: i64 = k as i64;
        let mut small_sum: i64 = 0;
        let mut value: usize = 1;
        while value <= 100 && remaining_small > 0
            invariant
                1 <= nums.len() <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                1 <= k <= nums.len(),
                freq.len() == 101,
                forall |x: int| 0 <= x < 101 ==> 0 <= #[trigger] freq[x] <= nums.len(),
                forall |v: int| 1 <= v <= 100 ==> #[trigger] freq[v] as int == Self::count_value(nums@, v),
                1 <= value <= 101,
                0 <= remaining_small as int <= k as int,
                0 <= small_sum as int,
                small_sum as int <= (k as int - remaining_small as int) * 100,
                small_sum as int + Self::sum_smallest_from(nums@, remaining_small as int, value as int) == total_small,
            decreases 101 - value,
        {
            let count_here = freq[value];
            let take = if remaining_small < count_here {
                remaining_small
            } else {
                count_here
            };

            let ghost old_remaining = remaining_small as int;
            let ghost old_small_sum = small_sum as int;
            let ghost old_value = value as int;
            let ghost old_take = take as int;

            proof {
                assert(1 <= old_value <= 100);
                assert(count_here as int == Self::count_value(nums@, old_value));
                assert(0 <= count_here);
                if remaining_small < count_here {
                    assert(old_take == old_remaining);
                } else {
                    assert(old_take == count_here as int);
                }
                assert(old_take == Self::min_int(old_remaining, count_here as int));
                assert(0 <= old_take <= old_remaining);
                assert(old_take * old_value <= old_take * 100) by(nonlinear_arith)
                    requires
                        0 <= old_take,
                        old_value <= 100,
                {};
                assert(Self::sum_smallest_from(nums@, old_remaining, old_value)
                    == Self::min_int(old_remaining, Self::count_value(nums@, old_value)) * old_value
                        + Self::sum_smallest_from(
                            nums@,
                            old_remaining - Self::min_int(old_remaining, Self::count_value(nums@, old_value)),
                            old_value + 1,
                        ));
            }

            small_sum = small_sum + take * value as i64;
            remaining_small = remaining_small - take;
            value = value + 1;

            proof {
                assert(small_sum as int == old_small_sum + old_take * old_value);
                assert(remaining_small as int == old_remaining - old_take);
                assert(value as int == old_value + 1);
                assert(0 <= remaining_small as int <= k as int);
                assert(old_small_sum <= (k as int - old_remaining) * 100);
                assert(old_small_sum + old_take * old_value
                    <= (k as int - old_remaining) * 100 + old_take * 100) by(nonlinear_arith)
                    requires
                        old_small_sum <= (k as int - old_remaining) * 100,
                        old_take >= 0,
                        old_value <= 100;
                assert((k as int - old_remaining) * 100 + old_take * 100
                    == (k as int - (old_remaining - old_take)) * 100) by(nonlinear_arith);
                assert(small_sum as int <= (k as int - remaining_small as int) * 100);
                assert(small_sum as int + Self::sum_smallest_from(nums@, remaining_small as int, value as int)
                    == total_small);
            }
        }

        proof {
            assert(!(value <= 100 && remaining_small > 0));
            if remaining_small > 0 {
                assert(value > 100);
                assert(Self::sum_smallest_from(nums@, remaining_small as int, value as int) == 0);
            } else {
                assert(remaining_small <= 0);
                assert(remaining_small as int == 0);
                assert(Self::sum_smallest_from(nums@, remaining_small as int, value as int) == 0);
            }
            assert(small_sum as int == total_small);
            assert(small_sum as int <= k as int * 100);
        }

        let mut remaining_large: i64 = k as i64;
        let mut large_sum: i64 = 0;
        let mut value_high: i32 = 100;
        while value_high >= 1 && remaining_large > 0
            invariant
                1 <= nums.len() <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                1 <= k <= nums.len(),
                freq.len() == 101,
                forall |x: int| 0 <= x < 101 ==> 0 <= #[trigger] freq[x] <= nums.len(),
                forall |v: int| 1 <= v <= 100 ==> #[trigger] freq[v] as int == Self::count_value(nums@, v),
                0 <= value_high <= 100,
                0 <= remaining_large as int <= k as int,
                0 <= large_sum as int,
                large_sum as int <= (k as int - remaining_large as int) * 100,
                large_sum as int + Self::sum_largest_from(nums@, remaining_large as int, value_high as int) == total_large,
            decreases value_high,
        {
            let idx = value_high as usize;
            let count_here = freq[idx];
            let take = if remaining_large < count_here {
                remaining_large
            } else {
                count_here
            };

            let ghost old_remaining = remaining_large as int;
            let ghost old_large_sum = large_sum as int;
            let ghost old_value = value_high as int;
            let ghost old_take = take as int;

            proof {
                assert(1 <= old_value <= 100);
                assert(count_here as int == Self::count_value(nums@, old_value));
                assert(0 <= count_here);
                if remaining_large < count_here {
                    assert(old_take == old_remaining);
                } else {
                    assert(old_take == count_here as int);
                }
                assert(old_take == Self::min_int(old_remaining, count_here as int));
                assert(0 <= old_take <= old_remaining);
                assert(old_take * old_value <= old_take * 100) by(nonlinear_arith)
                    requires
                        0 <= old_take,
                        old_value <= 100,
                {};
                assert(Self::sum_largest_from(nums@, old_remaining, old_value)
                    == Self::min_int(old_remaining, Self::count_value(nums@, old_value)) * old_value
                        + Self::sum_largest_from(
                            nums@,
                            old_remaining - Self::min_int(old_remaining, Self::count_value(nums@, old_value)),
                            old_value - 1,
                        ));
            }

            large_sum = large_sum + take * value_high as i64;
            remaining_large = remaining_large - take;
            value_high = value_high - 1;

            proof {
                assert(large_sum as int == old_large_sum + old_take * old_value);
                assert(remaining_large as int == old_remaining - old_take);
                assert(value_high as int == old_value - 1);
                assert(0 <= remaining_large as int <= k as int);
                assert(old_large_sum <= (k as int - old_remaining) * 100);
                assert(old_large_sum + old_take * old_value
                    <= (k as int - old_remaining) * 100 + old_take * 100) by(nonlinear_arith)
                    requires
                        old_large_sum <= (k as int - old_remaining) * 100,
                        old_take >= 0,
                        old_value <= 100;
                assert((k as int - old_remaining) * 100 + old_take * 100
                    == (k as int - (old_remaining - old_take)) * 100) by(nonlinear_arith);
                assert(large_sum as int <= (k as int - remaining_large as int) * 100);
                assert(large_sum as int + Self::sum_largest_from(nums@, remaining_large as int, value_high as int)
                    == total_large);
            }
        }

        proof {
            assert(!(value_high >= 1 && remaining_large > 0));
            if remaining_large > 0 {
                assert(value_high < 1);
                assert(Self::sum_largest_from(nums@, remaining_large as int, value_high as int) == 0);
            } else {
                assert(remaining_large <= 0);
                assert(remaining_large as int == 0);
                assert(Self::sum_largest_from(nums@, remaining_large as int, value_high as int) == 0);
            }
            assert(large_sum as int == total_large);
            assert(large_sum as int <= k as int * 100);
        }

        let diff = if large_sum >= small_sum {
            large_sum - small_sum
        } else {
            small_sum - large_sum
        };

        proof {
            assert(large_sum as int == total_large);
            assert(small_sum as int == total_small);
            assert(0 <= small_sum as int <= k as int * 100);
            assert(0 <= large_sum as int <= k as int * 100);
            if large_sum >= small_sum {
                assert(diff as int == large_sum as int - small_sum as int);
                assert(diff as int <= large_sum as int);
                assert(diff as int <= k as int * 100);
                assert(total_large - total_small >= 0);
                assert(Self::abs_int(total_large - total_small) == total_large - total_small);
                assert(diff as int == total_large - total_small);
            } else {
                assert(diff as int == small_sum as int - large_sum as int);
                assert(diff as int <= small_sum as int);
                assert(diff as int <= k as int * 100);
                assert(total_large - total_small < 0);
                assert(Self::abs_int(total_large - total_small) == total_small - total_large);
                assert(diff as int == total_small - total_large);
            }
            assert(k as int * 100 <= 10000) by(nonlinear_arith)
                requires
                    k as int <= 100,
            {};
            assert(diff as int <= 10000);
            assert(diff <= i32::MAX as i64);
        }

        diff as i32
    }
}

} 
