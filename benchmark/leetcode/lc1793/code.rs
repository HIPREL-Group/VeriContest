impl Solution {
    pub fn maximum_score(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let k_usize = k as usize;
        let mut left: usize = k_usize;
        let mut right: usize = k_usize;
        let mut cur_min: i32 = nums[k_usize];
        let mut result: i32 = cur_min;

        while left > 0 || right < n - 1 {
            let left_val: i32 = if left > 0 { nums[left - 1] } else { 0 };
            let right_val: i32 = if right < n - 1 { nums[right + 1] } else { 0 };

            if left_val >= right_val {
                left = left - 1;
                if nums[left] < cur_min {
                    cur_min = nums[left];
                }
            } else {
                right = right + 1;
                if nums[right] < cur_min {
                    cur_min = nums[right];
                }
            }

            let score: i32 = cur_min * ((right - left + 1) as i32);

            if score > result {
                result = score;
            }
        }

        result
    }
}
