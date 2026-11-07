impl Solution {
    pub fn find_max_average_core(nums: Vec<i32>, k: i32) -> i64
    {
        let n = nums.len();
        let k_usize = k as usize;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < k_usize
        {
            sum = sum + (nums[i] as i64);
            i = i + 1;
        }
        let mut max_sum: i64 = sum;
        let mut j: usize = 1;
        while j <= n - k_usize
        {
            sum = sum - (nums[j - 1] as i64) + (nums[j + k_usize - 1] as i64);
            if sum > max_sum {
                max_sum = sum;
            }
            j = j + 1;
        }
        max_sum
    }
}

impl Solution {
    pub fn find_max_average(nums: Vec<i32>, k: i32) -> f64 {
        (Solution::find_max_average_core(nums, k) as f64) / (k as f64)
    }
}
