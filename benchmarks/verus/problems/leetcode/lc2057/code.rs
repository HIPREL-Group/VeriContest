impl Solution {
    pub fn smallest_equal(nums: Vec<i32>) -> i32 {
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] == (i % 10) as i32 {
                return i as i32;
            }
            i = i + 1;
        }
        -1
    }
}
