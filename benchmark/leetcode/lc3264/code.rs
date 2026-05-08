impl Solution {
    pub fn get_final_state(nums: Vec<i32>, k: i32, multiplier: i32) -> Vec<i32> {
        let mut nums = nums;
        let n = nums.len();
        let mut step: i32 = 0;
        while step < k {
            let mut min_idx: usize = 0;
            let mut j: usize = 1;
            while j < n {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j = j + 1;
            }
            let old_val: i32 = nums[min_idx];
            let new_val: i32 = old_val * multiplier;
            nums[min_idx] = new_val;
            step = step + 1;
        }
        nums
    }
}
