impl Solution {
    pub fn maximum_count(nums: Vec<i32>) -> i32 {
        let mut neg: i32 = 0;
        let mut pos: i32 = 0;
        let mut i = 0;
        while i < nums.len() {
            if nums[i] < 0 {
                neg += 1;
            } else if nums[i] > 0 {
                pos += 1;
            }
            i += 1;
        }
        if pos >= neg { pos } else { neg }
    }
}
