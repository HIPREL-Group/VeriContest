impl Solution {
    pub fn minimum_deletions(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut min_idx: usize = 0;
        let mut max_idx: usize = 0;
        let mut i: usize = 1;

        while i < n {
            if nums[i] < nums[min_idx] {
                min_idx = i;
            }
            if nums[i] > nums[max_idx] {
                max_idx = i;
            }
            i += 1;
        }

        let small = if min_idx <= max_idx { min_idx } else { max_idx };
        let large = if min_idx <= max_idx { max_idx } else { min_idx };

        let left = large + 1;
        let right = n - small;
        let both = small + 1 + n - large;

        let ans = if left <= right && left <= both {
            left
        } else if right <= both {
            right
        } else {
            both
        };

        ans as i32
    }
}
