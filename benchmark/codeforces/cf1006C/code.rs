impl Solution {
    pub fn max_equal_outer_sum(nums: Vec<i64>) -> i64 {
        let n = nums.len();
        let mut pref: Vec<i64> = Vec::new();
        pref.push(0);
        let mut i = 0usize;
        while i < n {
            let next = pref[i] + nums[i];
            pref.push(next);
            i = i + 1;
        }
        let total = pref[n];
        let mut left = 0usize;
        let mut right = n;
        let mut ans = 0i64;
        while left <= right {
            let lsum = pref[left];
            let rsum = total - pref[right];
            if lsum < rsum {
                left = left + 1;
            } else if lsum > rsum {
                right = right - 1;
            } else {
                if lsum > ans {
                    ans = lsum;
                }
                left = left + 1;
            }
        }
        ans
    }
}
