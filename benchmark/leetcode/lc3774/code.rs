impl Solution {
    pub fn abs_difference(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut freq: Vec<i64> = vec![0; 101];
        let mut i: usize = 0;
        while i < n {
            let idx = nums[i] as usize;
            freq[idx] = freq[idx] + 1;
            i = i + 1;
        }

        let mut remaining_small: i64 = k as i64;
        let mut small_sum: i64 = 0;
        let mut value: usize = 1;
        while value <= 100 && remaining_small > 0 {
            let count_here = freq[value];
            let take = if remaining_small < count_here {
                remaining_small
            } else {
                count_here
            };
            small_sum = small_sum + take * value as i64;
            remaining_small = remaining_small - take;
            value = value + 1;
        }

        let mut remaining_large: i64 = k as i64;
        let mut large_sum: i64 = 0;
        let mut value_high: i32 = 100;
        while value_high >= 1 && remaining_large > 0 {
            let idx = value_high as usize;
            let count_here = freq[idx];
            let take = if remaining_large < count_here {
                remaining_large
            } else {
                count_here
            };
            large_sum = large_sum + take * value_high as i64;
            remaining_large = remaining_large - take;
            value_high = value_high - 1;
        }

        let diff = if large_sum >= small_sum {
            large_sum - small_sum
        } else {
            small_sum - large_sum
        };

        diff as i32
    }
}
