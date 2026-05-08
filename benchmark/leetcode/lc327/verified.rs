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

    proof fn lemma_count_for_start_nonneg(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int)
        requires
            0 <= i < nums.len(),
            i <= end_excl <= nums.len(),
        ensures
            0 <= Self::spec_count_for_start(nums, lower, upper, i, end_excl),
        decreases end_excl - i,
    {
        if end_excl > i {
            Self::lemma_count_for_start_nonneg(nums, lower, upper, i, end_excl - 1);
        }
    }

    proof fn lemma_count_for_start_mono(nums: Seq<i32>, lower: int, upper: int, i: int, end1: int, end2: int)
        requires
            0 <= i < nums.len(),
            i <= end1 <= end2 <= nums.len(),
        ensures
            Self::spec_count_for_start(nums, lower, upper, i, end1)
                <= Self::spec_count_for_start(nums, lower, upper, i, end2),
        decreases end2 - end1,
    {
        if end2 > end1 {
            Self::lemma_count_for_start_mono(nums, lower, upper, i, end1, end2 - 1);
            Self::lemma_count_for_start_nonneg(nums, lower, upper, i, end2);
            assert(Self::spec_count_for_start(nums, lower, upper, i, end2)
                == Self::spec_count_for_start(nums, lower, upper, i, end2 - 1)
                    + if lower <= Self::spec_segment_sum(nums, i, end2) <= upper { 1int } else { 0int });
            assert(Self::spec_count_for_start(nums, lower, upper, i, end2 - 1)
                <= Self::spec_count_for_start(nums, lower, upper, i, end2));
        }
    }

    proof fn lemma_prefix_nonneg(nums: Seq<i32>, lower: int, upper: int, upto: int)
        requires
            0 <= upto <= nums.len(),
        ensures
            0 <= Self::spec_count_starts_prefix(nums, lower, upper, upto),
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_prefix_nonneg(nums, lower, upper, upto - 1);
            Self::lemma_count_for_start_nonneg(nums, lower, upper, upto - 1, nums.len() as int);
        }
    }

    proof fn lemma_prefix_mono(nums: Seq<i32>, lower: int, upper: int, u1: int, u2: int)
        requires
            0 <= u1 <= u2 <= nums.len(),
        ensures
            Self::spec_count_starts_prefix(nums, lower, upper, u1)
                <= Self::spec_count_starts_prefix(nums, lower, upper, u2),
        decreases u2 - u1,
    {
        if u2 > u1 {
            Self::lemma_prefix_mono(nums, lower, upper, u1, u2 - 1);
            Self::lemma_count_for_start_nonneg(nums, lower, upper, u2 - 1, nums.len() as int);
            assert(Self::spec_count_starts_prefix(nums, lower, upper, u2)
                == Self::spec_count_starts_prefix(nums, lower, upper, u2 - 1)
                    + Self::spec_count_for_start(nums, lower, upper, u2 - 1, nums.len() as int));
            assert(Self::spec_count_starts_prefix(nums, lower, upper, u2 - 1)
                <= Self::spec_count_starts_prefix(nums, lower, upper, u2));
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
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
        let mut ans: i64 = 0;
        let lo = lower as i64;
        let hi = upper as i64;

        let mut i: usize = 0;
        while i < n
            invariant
                1 <= nums.len() <= 100000,
                n == nums.len(),
                forall|k: int| 0 <= k < nums.len() ==> -2147483648 <= #[trigger] nums[k] <= 2147483647,
                0 <= i <= n,
                lo == lower as i64,
                hi == upper as i64,
                ans as int == Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int),
                0 <= ans,
                Self::spec_count_range_sum(nums@, lower as int, upper as int) <= i32::MAX,
        {
            proof {
                Self::lemma_prefix_mono(nums@, lower as int, upper as int, i as int, n as int);
                assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int)
                    <= Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int));
                assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int)
                    == Self::spec_count_range_sum(nums@, lower as int, upper as int));
            }
            let mut s: i64 = 0;
            let mut j: usize = i;
            while j < n
                invariant
                    1 <= nums.len() <= 100000,
                    n == nums.len(),
                    forall|k: int| 0 <= k < nums.len() ==> -2147483648 <= #[trigger] nums[k] <= 2147483647,
                    0 <= i < n,
                    i <= j <= n,
                    lo == lower as i64,
                    hi == upper as i64,
                    s as int == Self::spec_segment_sum(nums@, i as int, j as int),
                    ans as int
                        == Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int)
                            + Self::spec_count_for_start(nums@, lower as int, upper as int, i as int, j as int),
                    0 <= ans,
                    ans as int <= i32::MAX,
                    -2147483648 * ((j as int) - (i as int)) <= s as int,
                    s as int <= 2147483647 * ((j as int) - (i as int)),
                    Self::spec_count_range_sum(nums@, lower as int, upper as int) <= i32::MAX,
            {
                proof {
                    assert(-2147483648 <= nums[j as int] <= 2147483647);
                    assert(-2147483648 * ((j as int) - (i as int)) <= s as int);
                    assert(s as int <= 2147483647 * ((j as int) - (i as int)));
                    assert(-2147483648 * (((j as int) + 1) - (i as int))
                        <= s as int + nums[j as int] as int) by (nonlinear_arith)
                        requires
                            -2147483648 * ((j as int) - (i as int)) <= s as int,
                            -2147483648 <= nums[j as int],
                    {
                    }
                    assert(s as int + nums[j as int] as int
                        <= 2147483647 * (((j as int) + 1) - (i as int))) by (nonlinear_arith)
                        requires
                            s as int <= 2147483647 * ((j as int) - (i as int)),
                            nums[j as int] <= 2147483647,
                    {
                    }
                    assert(ans as int <= i32::MAX);
                    assert(ans <= i32::MAX as i64) by (nonlinear_arith)
                        requires
                            0 <= ans,
                            ans as int <= i32::MAX,
                    {
                    }
                    assert(ans < 9223372036854775807) by (nonlinear_arith)
                        requires
                            ans <= i32::MAX as i64,
                    {
                    }
                }
                s += nums[j] as i64;
                if lo <= s && s <= hi {
                    ans += 1;
                }
                proof {
                    assert(Self::spec_segment_sum(nums@, i as int, j as int + 1)
                        == Self::spec_segment_sum(nums@, i as int, j as int) + nums[j as int] as int);
                    assert(s as int == Self::spec_segment_sum(nums@, i as int, j as int + 1));
                    assert((if lower as int <= Self::spec_segment_sum(nums@, i as int, j as int + 1) <= upper as int { 1int } else { 0int })
                        == (if lo <= s && s <= hi { 1int } else { 0int }));
                    assert(Self::spec_count_for_start(nums@, lower as int, upper as int, i as int, j as int + 1)
                        == Self::spec_count_for_start(nums@, lower as int, upper as int, i as int, j as int)
                            + (if lower as int <= Self::spec_segment_sum(nums@, i as int, j as int + 1) <= upper as int { 1int } else { 0int }));
                    Self::lemma_count_for_start_mono(nums@, lower as int, upper as int, i as int, j as int + 1, n as int);
                    Self::lemma_prefix_mono(nums@, lower as int, upper as int, i as int + 1, n as int);
                    assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int)
                        + Self::spec_count_for_start(nums@, lower as int, upper as int, i as int, j as int + 1)
                        <= Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int + 1));
                    assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int + 1)
                        <= Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int));
                    assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int)
                        == Self::spec_count_range_sum(nums@, lower as int, upper as int));
                    assert(ans as int <= Self::spec_count_range_sum(nums@, lower as int, upper as int));
                    assert(ans as int <= i32::MAX);
                }
                j += 1;
            }
            proof {
                assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int + 1)
                    == Self::spec_count_starts_prefix(nums@, lower as int, upper as int, i as int)
                        + Self::spec_count_for_start(nums@, lower as int, upper as int, i as int, n as int));
                Self::lemma_prefix_nonneg(nums@, lower as int, upper as int, i as int + 1);
                Self::lemma_prefix_mono(nums@, lower as int, upper as int, i as int + 1, n as int);
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(ans as int == Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int));
            assert(Self::spec_count_starts_prefix(nums@, lower as int, upper as int, n as int)
                == Self::spec_count_range_sum(nums@, lower as int, upper as int));
            assert(ans as int <= i32::MAX);
        }

        ans as i32
    }
}

#[cfg(any())]
impl Solution {
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

    pub fn count_range_sum(nums: Vec<i32>, lower: i32, upper: i32) -> i32 {
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

#[cfg(any())]
impl Solution {
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
