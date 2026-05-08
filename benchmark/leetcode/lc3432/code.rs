impl Solution {
    pub fn count_partitions(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            total += nums[i];
            i += 1;
        }
        if (total as u32) % 2 == 0 {
            (n - 1) as i32
        } else {
            0
        }
    }
}
