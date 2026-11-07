impl Solution {
    pub fn minimum_operations(nums: Vec<i32>) -> i32 {
        let mut count: i32 = 0;
        for i in 0..nums.len() {
            if nums[i] % 3 != 0 {
                count += 1;
            }
        }
        return count;
    }
}
