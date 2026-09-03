impl Solution {
    fn sort_count(sums: &mut Vec<i64>, buf: &mut Vec<i64>, l: usize, r: usize, lower: i64, upper: i64) -> i64
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

    pub fn count_range_sum(nums: Vec<i32>, lower: i32, upper: i32) -> i32
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
