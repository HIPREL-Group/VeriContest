use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn spec_max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn array_value_upto(s: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else { array_value_upto(s, n - 1) + abs_diff(s[n - 1] as int, s[n] as int) }
}

pub open spec fn array_value(s: Seq<i32>) -> int {
    array_value_upto(s, s.len() as int - 1)
}

pub open spec fn reversal_gain(s: Seq<i32>, l: int, r: int) -> int {
    let n = s.len() as int;
    let left_change = if l > 0 {
        abs_diff(s[l - 1] as int, s[r] as int) - abs_diff(s[l - 1] as int, s[l] as int)
    } else { 0int };
    let right_change = if r < n - 1 {
        abs_diff(s[l] as int, s[r + 1] as int) - abs_diff(s[r] as int, s[r + 1] as int)
    } else { 0int };
    left_change + right_change
}

proof fn four_number_bound(a: int, b: int, c: int, d: int)
    ensures
        abs_diff(a, c) + abs_diff(b, d) - abs_diff(a, b) - abs_diff(c, d)
            <= 2 * spec_max(0, spec_max(
                spec_min(a, b) - spec_max(c, d),
                spec_min(c, d) - spec_max(a, b)
            )),
{
}

proof fn four_number_exact(a: int, b: int, c: int, d: int)
    requires
        spec_min(a, b) > spec_max(c, d),
    ensures
        abs_diff(a, c) + abs_diff(b, d) - abs_diff(a, b) - abs_diff(c, d)
            == 2 * (spec_min(a, b) - spec_max(c, d)),
{
}

impl Solution {
    pub fn max_value_after_reverse(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums@.len() <= 30000,
            forall |i: int| 0 <= i < nums@.len() ==> -100000 <= #[trigger] nums@[i] <= 100000,
            forall |l: int, r: int| 0 <= l && l <= r && r < nums@.len() ==>
                array_value(nums@) + #[trigger] reversal_gain(nums@, l, r) <= i32::MAX as int,
        ensures
            forall |l: int, r: int| 0 <= l && l <= r && r < nums@.len() ==>
                result as int >= array_value(nums@) + #[trigger] reversal_gain(nums@, l, r),
            exists |l: int, r: int| 0 <= l && l <= r && r < nums@.len() &&
                result as int == array_value(nums@) + reversal_gain(nums@, l, r),
    {
        let n = nums.len();
        let mut total: i64 = 0;
        let mut gain: i64 = 0;
        let mut min_of_max: i64 = 200001;
        let mut max_of_min: i64 = -200001;

        let ghost mut gl: int = 0;
        let ghost mut gr: int = 0;
        let ghost mut mom_idx: int = 0;
        let ghost mut mim_idx: int = 0;

        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                n == nums@.len(),
                n >= 2,
                n <= 30000,
                forall |j: int| 0 <= j < n as int ==> -100000 <= #[trigger] nums@[j] <= 100000,
                total as int == array_value_upto(nums@, i as int),
                total >= 0i64,
                total as int <= 200000 * (i as int),
                0 <= gain <= 200_000i64,
                forall |k: int| 0 <= k < i as int ==>
                    gain as int >= #[trigger] reversal_gain(nums@, 0, k),
                forall |k: int| 1 <= k && k <= i as int ==>
                    gain as int >= #[trigger] reversal_gain(nums@, k, (n - 1) as int),
                0 <= gl && gl <= gr && gr < n as int,
                gain as int == reversal_gain(nums@, gl, gr),
                forall |k: int| 0 <= k < i as int ==>
                    min_of_max as int <= #[trigger] spec_max(nums@[k] as int, nums@[k + 1] as int),
                forall |k: int| 0 <= k < i as int ==>
                    max_of_min as int >= #[trigger] spec_min(nums@[k] as int, nums@[k + 1] as int),
                i > 0 ==> (0 <= mim_idx < i as int &&
                    min_of_max as int == spec_max(nums@[mim_idx] as int, nums@[mim_idx + 1] as int)),
                i > 0 ==> (0 <= mom_idx < i as int &&
                    max_of_min as int == spec_min(nums@[mom_idx] as int, nums@[mom_idx + 1] as int)),
                i == 0 ==> (min_of_max == 200001i64 && max_of_min == -200001i64),
            decreases n - 1 - i,
        {
            let a = nums[i] as i64;
            let b = nums[i + 1] as i64;
            let diff: i64 = if a >= b { a - b } else { b - a };

            proof {
                assert(diff as int == abs_diff(nums@[i as int] as int, nums@[i as int + 1] as int));
                assert(diff as int <= 200000);
                assert(total as int + diff as int == array_value_upto(nums@, i as int + 1));
                assert(total as int + diff as int <= 200000 * (i as int) + 200000);
                assert(total as int + diff as int <= 6_000_000_000int) by(nonlinear_arith)
                    requires
                        total as int + diff as int <= 200000 * (i as int) + 200000,
                        (i as int) < (n as int) - 1,
                        (n as int) <= 30000;
            }

            total = total + diff;

            let first = nums[0] as i64;
            let last = nums[n - 1] as i64;
            let g1: i64 = (if first >= b { first - b } else { b - first }) - diff;
            let g2: i64 = (if last >= a { last - a } else { a - last }) - diff;

            proof {
                assert(g1 as int == reversal_gain(nums@, 0, i as int));
                assert(g2 as int == reversal_gain(nums@, (i + 1) as int, (n - 1) as int));
            }

            if g1 > gain {
                gain = g1;
                proof { gl = 0; gr = i as int; }
            }
            if g2 > gain {
                gain = g2;
                proof { gl = (i + 1) as int; gr = (n - 1) as int; }
            }

            let pair_max: i64 = if a >= b { a } else { b };
            let pair_min: i64 = if a <= b { a } else { b };

            proof {
                assert(pair_max as int == spec_max(nums@[i as int] as int, nums@[i as int + 1] as int));
                assert(pair_min as int == spec_min(nums@[i as int] as int, nums@[i as int + 1] as int));
            }

            if pair_max < min_of_max {
                min_of_max = pair_max;
                proof { mim_idx = i as int; }
            }
            if pair_min > max_of_min {
                max_of_min = pair_min;
                proof { mom_idx = i as int; }
            }

            i = i + 1;
        }

        proof {
            assert(i == n - 1);
            assert(total as int == array_value_upto(nums@, (n - 1) as int));
            assert(total as int == array_value(nums@));
        }

        let interior: i64 = if max_of_min > min_of_max {
            2 * (max_of_min - min_of_max)
        } else {
            0
        };

        let ghost old_gain = gain;

        if interior > gain {
            gain = interior;
            proof {
                assert(mom_idx != mim_idx) by {
                    if mom_idx == mim_idx {
                        assert(max_of_min as int == spec_min(nums@[mom_idx] as int, nums@[mom_idx + 1] as int));
                        assert(min_of_max as int == spec_max(nums@[mim_idx] as int, nums@[mim_idx + 1] as int));
                        assert(spec_min(nums@[mom_idx] as int, nums@[mom_idx + 1] as int)
                            <= spec_max(nums@[mom_idx] as int, nums@[mom_idx + 1] as int));
                        assert(max_of_min <= min_of_max);
                    }
                }
                if mom_idx < mim_idx {
                    gl = mom_idx + 1;
                    gr = mim_idx;
                    four_number_exact(
                        nums@[mom_idx] as int, nums@[mom_idx + 1] as int,
                        nums@[mim_idx] as int, nums@[mim_idx + 1] as int
                    );
                    assert(reversal_gain(nums@, gl, gr) == 2 * (max_of_min as int - min_of_max as int));
                } else {
                    gl = mim_idx + 1;
                    gr = mom_idx;
                    four_number_exact(
                        nums@[mom_idx] as int, nums@[mom_idx + 1] as int,
                        nums@[mim_idx] as int, nums@[mim_idx + 1] as int
                    );
                    assert(abs_diff(nums@[mom_idx] as int, nums@[mim_idx] as int)
                        == abs_diff(nums@[mim_idx] as int, nums@[mom_idx] as int));
                    assert(abs_diff(nums@[mom_idx + 1] as int, nums@[mim_idx + 1] as int)
                        == abs_diff(nums@[mim_idx + 1] as int, nums@[mom_idx + 1] as int));
                    assert(reversal_gain(nums@, gl, gr) == 2 * (max_of_min as int - min_of_max as int));
                }
                assert(gain as int == reversal_gain(nums@, gl, gr));
            }
        }

        proof {
            assert forall |l: int, r: int| 0 <= l && l <= r && r < n as int implies
                gain as int >= #[trigger] reversal_gain(nums@, l, r) by {
                if l == r {
                    assert(reversal_gain(nums@, l, r) == 0int);
                } else if l == 0 && r == n - 1 {
                    assert(reversal_gain(nums@, l, r) == 0int);
                } else if l == 0 {
                    assert(0 <= r && r < (n - 1) as int);
                    assert(old_gain as int >= reversal_gain(nums@, 0, r));
                    assert(gain >= old_gain);
                } else if r == n - 1 {
                    assert(1 <= l && l <= (n - 1) as int);
                    assert(old_gain as int >= reversal_gain(nums@, l, (n - 1) as int));
                    assert(gain >= old_gain);
                } else {
                    four_number_bound(
                        nums@[l - 1] as int, nums@[l] as int,
                        nums@[r] as int, nums@[r + 1] as int
                    );
                    let kl = l - 1;
                    let kr = r;
                    assert(0 <= kl && kl < (n - 1) as int);
                    assert(0 <= kr && kr < (n - 1) as int);
                    assert(max_of_min as int >= spec_min(nums@[kl] as int, nums@[kl + 1] as int));
                    assert(min_of_max as int <= spec_max(nums@[kr] as int, nums@[kr + 1] as int));
                    assert(max_of_min as int >= spec_min(nums@[kr] as int, nums@[kr + 1] as int));
                    assert(min_of_max as int <= spec_max(nums@[kl] as int, nums@[kl + 1] as int));
                    assert(spec_min(nums@[kl] as int, nums@[kl + 1] as int)
                        - spec_max(nums@[kr] as int, nums@[kr + 1] as int)
                        <= max_of_min as int - min_of_max as int);
                    assert(spec_min(nums@[kr] as int, nums@[kr + 1] as int)
                        - spec_max(nums@[kl] as int, nums@[kl + 1] as int)
                        <= max_of_min as int - min_of_max as int);
                    if max_of_min > min_of_max {
                        assert(gain as int >= 2 * (max_of_min as int - min_of_max as int));
                    }
                }
            };

            assert(total as int + gain as int >= 0) by {
                assert(total >= 0);
                assert(gain >= 0);
            }
            assert(total as int + gain as int <= i32::MAX as int) by {
                assert(total as int == array_value(nums@));
                assert(gain as int == reversal_gain(nums@, gl, gr));
                assert(0 <= gl && gl <= gr && gr < n as int);
            }
        }

        (total + gain) as i32
    }
}

}
