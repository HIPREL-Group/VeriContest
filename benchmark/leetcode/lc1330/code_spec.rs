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
        let mut i: usize = 0;
        while i < n - 1 {
            let a = nums[i] as i64;
            let b = nums[i + 1] as i64;
            let diff: i64 = if a >= b { a - b } else { b - a };
            total = total + diff;
            let first = nums[0] as i64;
            let last = nums[n - 1] as i64;
            let g1: i64 = (if first >= b { first - b } else { b - first }) - diff;
            let g2: i64 = (if last >= a { last - a } else { a - last }) - diff;
            if g1 > gain {
                gain = g1;
            }
            if g2 > gain {
                gain = g2;
            }
            let pair_max: i64 = if a >= b { a } else { b };
            let pair_min: i64 = if a <= b { a } else { b };
            if pair_max < min_of_max {
                min_of_max = pair_max;
            }
            if pair_min > max_of_min {
                max_of_min = pair_min;
            }
            i = i + 1;
        }
        let interior: i64 = if max_of_min > min_of_max {
            2 * (max_of_min - min_of_max)
        } else {
            0
        };
        if interior > gain {
            gain = interior;
        }
        (total + gain) as i32
    }
}

}
