use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_good(nums: Seq<i32>, k: int, i: int) -> bool {
    (if i < k {
        true
    } else {
        nums[i] > nums[i - k]
    }) && (if i + k >= nums.len() {
        true
    } else {
        nums[i] > nums[i + k]
    })
}

pub open spec fn spec_sum_good_prefix(nums: Seq<i32>, k: int, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        spec_sum_good_prefix(nums, k, end - 1)
            + (if is_good(nums, k, end - 1) {
                nums[end - 1] as int
            } else {
                0
            })
    }
}

proof fn lemma_sum_good_step(nums: Seq<i32>, k: int, i: int)
    requires
        0 <= i < nums.len(),
        1 <= k,
    ensures
        spec_sum_good_prefix(nums, k, i + 1)
            == spec_sum_good_prefix(nums, k, i)
                + (if is_good(nums, k, i) {
                    nums[i] as int
                } else {
                    0
                }),
{
    reveal_with_fuel(spec_sum_good_prefix, 2);
}

proof fn lemma_sum_good_bounds(nums: Seq<i32>, k: int, end: int)
    requires
        0 <= end <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        1 <= k,
    ensures
        0 <= spec_sum_good_prefix(nums, k, end) <= 1000 * end,
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_sum_good_bounds(nums, k, end - 1);
        lemma_sum_good_step(nums, k, end - 1);
        let prev = spec_sum_good_prefix(nums, k, end - 1);
        let extra = if is_good(nums, k, end - 1) {
            nums[end - 1] as int
        } else {
            0int
        };
        if is_good(nums, k, end - 1) {
            assert(1 <= nums[end - 1] <= 1000);
            assert(extra == nums[end - 1] as int);
        } else {
            assert(extra == 0);
        }
        assert(0 <= extra <= 1000);
        assert(0 <= prev <= 1000 * (end - 1));
        assert(spec_sum_good_prefix(nums, k, end) == prev + extra);
        assert(prev + extra <= 1000 * end) by (nonlinear_arith)
            requires
                prev <= 1000 * (end - 1),
                extra <= 1000,
                0 <= end;
    }
}

impl Solution {
    pub fn sum_of_good_numbers(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            1 <= k,
            k as int <= nums.len() as int / 2,
        ensures
            result as int == spec_sum_good_prefix(nums@, k as int, nums.len() as int),
    {
        let n = nums.len();
        let kk: usize = k as usize;

        proof {
            assert(kk as int == k as int);
            assert(k as int <= n as int / 2);
            assert(n as int / 2 <= n as int);
            assert(kk <= n);
        }

        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 100,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
                1 <= k,
                k as int <= nums.len() as int / 2,
                kk as int == k as int,
                kk <= n,
                0 <= i <= n,
                sum as int == spec_sum_good_prefix(nums@, k as int, i as int),
                0 <= sum as int <= 100000,
            decreases n - i,
        {
            let left_ok: bool;
            if i >= kk {
                left_ok = nums[i] > nums[i - kk];
            } else {
                left_ok = true;
            }

            let right_ok: bool;
            if kk < n - i {
                right_ok = nums[i] > nums[i + kk];
            } else {
                right_ok = true;
            }

            let mut add: i32 = 0;
            if left_ok && right_ok {
                add = nums[i];
            }

            proof {
                let ii = i as int;
                assert(0 <= ii < n as int);
                assert(ii == i as int);

                if i >= kk {
                    assert(left_ok == (nums@[ii] > nums@[ii - (kk as int)]));
                    assert(ii >= kk as int);
                    assert(ii >= k as int);
                    assert((i - kk) as int == ii - kk as int);
                    assert(ii - kk as int == ii - k as int);
                    assert((if ii < k as int {
                        true
                    } else {
                        nums@[ii] > nums@[ii - k as int]
                    }) == left_ok);
                } else {
                    assert(left_ok);
                    assert(ii < kk as int);
                    assert(ii < k as int);
                    assert((if ii < k as int {
                        true
                    } else {
                        nums@[ii] > nums@[ii - k as int]
                    }) == left_ok);
                }

                if kk < n - i {
                    assert(right_ok == (nums@[ii] > nums@[ii + (kk as int)]));
                    assert(i + kk < n);
                    assert((i + kk) as int == ii + kk as int);
                    assert(ii + kk as int == ii + (k as int));
                    assert(ii + (k as int) < (n as int));
                    assert((if ii + (k as int) >= nums.len() {
                        true
                    } else {
                        nums@[ii] > nums@[ii + (k as int)]
                    }) == right_ok);
                } else {
                    assert(right_ok);
                    assert(kk as int >= n as int - i as int);
                    assert(ii + (k as int) >= n as int) by (nonlinear_arith)
                        requires
                            ii == i as int,
                            kk as int == k as int,
                            kk as int >= n as int - i as int;
                    assert((if ii + (k as int) >= nums.len() {
                        true
                    } else {
                        nums@[ii] > nums@[ii + (k as int)]
                    }) == right_ok);
                }

                let left_cond = if ii < k as int {
                    true
                } else {
                    nums@[ii] > nums@[ii - (k as int)]
                };
                let right_cond = if ii + (k as int) >= nums.len() {
                    true
                } else {
                    nums@[ii] > nums@[ii + (k as int)]
                };
                if i >= kk {
                    assert(left_cond == left_ok);
                } else {
                    assert(left_cond == left_ok);
                }
                if kk < n - i {
                    assert(right_cond == right_ok);
                } else {
                    assert(right_cond == right_ok);
                }
                assert((left_cond && right_cond) == (left_ok && right_ok));
                assert(is_good(nums@, k as int, ii) == (left_ok && right_ok));

                if left_ok && right_ok {
                    assert(1 <= nums@[ii] <= 1000);
                    assert(add as int == nums@[ii] as int);
                } else {
                    assert(add == 0);
                    assert(add as int == 0);
                }

                assert(add as int == if is_good(nums@, k as int, ii) {
                    nums@[ii] as int
                } else {
                    0int
                });

                lemma_sum_good_step(nums@, k as int, ii);
                assert(sum as int + add as int == spec_sum_good_prefix(nums@, k as int, ii + 1));
                lemma_sum_good_bounds(nums@, k as int, ii + 1);
                assert(ii + 1 <= n as int);
                assert(1000 * (ii + 1) <= 100000) by (nonlinear_arith)
                    requires
                        ii + 1 <= n as int,
                        n <= 100;
                assert(0 <= sum as int + add as int <= 100000);
                assert(sum as int + add as int <= 2147483647);
            }

            sum = sum + add;
            i = i + 1;
        }

        sum
    }
}

}
