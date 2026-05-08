impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            total += nums[i];
            i += 1;
        }
        ((total as u32) % (k as u32)) as i32
    }
}
