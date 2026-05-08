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
