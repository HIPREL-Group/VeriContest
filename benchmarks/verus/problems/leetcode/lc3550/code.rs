impl Solution {
    fn digit_sum_exec(x: i32) -> i32 {
        x / 1000 + (x / 100) % 10 + (x / 10) % 10 + x % 10
    }

    pub fn smallest_index(nums: Vec<i32>) -> i32 {
        let mut i: usize = 0;
        while i < nums.len() {
            let s = Self::digit_sum_exec(nums[i]);
            if s == i as i32 {
                return i as i32;
            }
            i = i + 1;
        }
        -1
    }
}
