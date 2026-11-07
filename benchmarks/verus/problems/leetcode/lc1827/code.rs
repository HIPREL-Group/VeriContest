impl Solution {
    pub fn min_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut ops: i64 = 0;
        let mut prev: i64 = nums[0] as i64;
        let mut i: usize = 1;
        while i < n {
            if nums[i] as i64 <= prev {
                ops = ops + (prev + 1 - nums[i] as i64);
                prev = prev + 1;
            } else {
                prev = nums[i] as i64;
            }
            i += 1;
        }
        ops as i32
    }
}
