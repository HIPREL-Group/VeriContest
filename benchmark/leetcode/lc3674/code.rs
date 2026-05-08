impl Solution {
    pub fn min_operations(nums: Vec<i32>) -> i32 {
        let mut i: usize = 1;
        while i < nums.len() {
            if nums[i] != nums[0] {
                return 1;
            }
            i = i + 1;
        }
        0
    }
}
