use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_segment_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::spec_segment_sum(nums, l, r - 1) + nums[r - 1] as int
        }
    }

    pub open spec fn spec_count_for_start(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int) -> int
        recommends
            0 <= i < nums.len(),
            i <= end_excl <= nums.len(),
        decreases end_excl - i,
    {
        if end_excl <= i {
            0
        } else {
            Self::spec_count_for_start(nums, lower, upper, i, end_excl - 1)
                + if lower <= Self::spec_segment_sum(nums, i, end_excl) <= upper {
                    1int
                } else {
                    0int
                }
        }
    }

    pub open spec fn spec_count_starts_prefix(nums: Seq<i32>, lower: int, upper: int, upto_i: int) -> int
        recommends
            0 <= upto_i <= nums.len(),
        decreases upto_i,
    {
        if upto_i <= 0 {
            0
        } else {
            Self::spec_count_starts_prefix(nums, lower, upper, upto_i - 1)
                + Self::spec_count_for_start(nums, lower, upper, upto_i - 1, nums.len() as int)
        }
    }

    pub open spec fn spec_count_range_sum(nums: Seq<i32>, lower: int, upper: int) -> int
        recommends
            1 <= nums.len(),
    {
        Self::spec_count_starts_prefix(nums, lower, upper, nums.len() as int)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn sort_count(
        sums: &mut Vec<i64>,
        buf: &mut Vec<i64>,
        l: usize,
        r: usize,
        lower: i64,
        upper: i64,
    ) -> i64 {
        if r - l <= 1 {
            return 0;
        }

        let mid = l + (r - l) / 2;
        let mut count = Self::sort_count(sums, buf, l, mid, lower, upper)
            + Self::sort_count(sums, buf, mid, r, lower, upper);

        let mut lo = mid;
        let mut hi = mid;
        for i in l..mid {
            while lo < r && sums[lo] - sums[i] < lower {
                lo += 1;
            }
            while hi < r && sums[hi] - sums[i] <= upper {
                hi += 1;
            }
            count += (hi - lo) as i64;
        }

        let mut i = l;
        let mut j = mid;
        let mut k = l;
        while i < mid && j < r {
            if sums[i] <= sums[j] {
                buf[k] = sums[i];
                i += 1;
            } else {
                buf[k] = sums[j];
                j += 1;
            }
            k += 1;
        }
        while i < mid {
            buf[k] = sums[i];
            i += 1;
            k += 1;
        }
        while j < r {
            buf[k] = sums[j];
            j += 1;
            k += 1;
        }

        for idx in l..r {
            sums[idx] = buf[idx];
        }
        count
    }

    pub fn count_range_sum(nums: Vec<i32>, lower: i32, upper: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100000,
            forall|i: int| 0 <= i < nums.len() ==> -2147483648 <= #[trigger] nums[i] <= 2147483647,
            -100000 <= lower as int <= upper as int <= 100000,
            Self::spec_count_range_sum(nums@, lower as int, upper as int) <= i32::MAX,
        ensures
            res as int == Self::spec_count_range_sum(nums@, lower as int, upper as int),
    {
        let n = nums.len();
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        for _ in 0..(n + 1) {
            prefix.push(0i64);
        }
        for i in 0..n {
            prefix[i + 1] = prefix[i] + nums[i] as i64;
        }

        let mut buf: Vec<i64> = Vec::with_capacity(n + 1);
        for _ in 0..(n + 1) {
            buf.push(0i64);
        }
        let mut res = Self::sort_count(&mut prefix, &mut buf, 0, n + 1, lower as i64, upper as i64) as i32;
        res
    }
}

}
