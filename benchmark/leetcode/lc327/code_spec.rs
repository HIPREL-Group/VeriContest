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

    fn sort_count(sums: &mut Vec<i64>, buf: &mut Vec<i64>, l: usize, r: usize, lower: i64, upper: i64) -> (count: i64)
        requires
            l <= r <= old(sums).len(),
            old(sums).len() <= 100001,
            old(buf).len() == old(sums).len(),
            -100000 <= lower <= upper <= 100000,
            forall|k: int| 0 <= k < old(sums).len() ==> -214748364800000 <= #[trigger] old(sums)[k] <= 214748364800000,
        ensures
            sums.len() == old(sums).len(),
            buf.len() == old(sums).len(),
            forall|k: int| (0 <= k < l as int || r as int <= k < sums.len() as int) ==> sums[k] == old(sums)[k],
            forall|k: int| 0 <= k < old(sums).len() ==> -214748364800000 <= #[trigger] sums[k] <= 214748364800000,
            Self::sorted_range(sums@, l as int, r as int),
            sums@.subrange(l as int, r as int).to_multiset() =~= old(sums)@.subrange(l as int, r as int).to_multiset(),
            count as int == Self::range_pair_count(old(sums)@, l as int, r as int, lower as int, upper as int),
            0 <= count as int <= (r as int - l as int) * (r as int - l as int),
        decreases r - l,
    {
        if r - l <= 1 {
            return 0;
        }

        let mid = l + (r - l) / 2;
        let count1 = Self::sort_count(sums, buf, l, mid, lower, upper);
        let count2 = Self::sort_count(sums, buf, mid, r, lower, upper);
        let mut count = count1 + count2;

        let mut lo: usize = mid;
        let mut hi: usize = mid;
        let mut i: usize = l;
        while i < mid
        {
            while lo < r && sums[lo] - sums[i] < lower
            {
                lo += 1;
            }

            while hi < r && sums[hi] - sums[i] <= upper
            {
                hi += 1;
            }
            count = count + ((hi - lo) as i64);
            i += 1;
        }

        let mut i2: usize = l;
        let mut j2: usize = mid;
        let mut k2: usize = l;
        while i2 < mid && j2 < r
        {
            if sums[i2] <= sums[j2] {
                buf[k2] = sums[i2];
                i2 += 1;
            } else {
                buf[k2] = sums[j2];
                j2 += 1;
            }
            k2 += 1;
        }
        while i2 < mid
        {
            buf[k2] = sums[i2];
            i2 += 1;
            k2 += 1;
        }
        while j2 < r
        {
            buf[k2] = sums[j2];
            j2 += 1;
            k2 += 1;
        }

        let mut idx2: usize = l;
        while idx2 < r
        {
            sums[idx2] = buf[idx2];
            idx2 += 1;
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
        let mut t: usize = 0;
        while t < n + 1
        {
            prefix.push(0i64);
            t += 1;
        }

        let mut i: usize = 0;
        while i < n
        {
            let v = prefix[i] + nums[i] as i64;
            prefix[i + 1] = v;
            i += 1;
        }

        let mut buf: Vec<i64> = Vec::with_capacity(n + 1);
        let mut t2: usize = 0;
        while t2 < n + 1
        {
            buf.push(0i64);
            t2 += 1;
        }

        let res_i64 = Self::sort_count(&mut prefix, &mut buf, 0, n + 1, lower as i64, upper as i64);

        res_i64 as i32
    }
}

}
