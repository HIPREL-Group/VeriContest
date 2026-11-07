impl Solution {
    pub fn is_array_special(nums: Vec<i32>) -> bool {
        let n = nums.len();
        let mut i: usize = 1;
        while i < n {
            if nums[i - 1] % 2 == nums[i] % 2 {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
