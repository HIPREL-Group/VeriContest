impl Solution {
    pub fn array_sign(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut sign: i32 = 1;
        let mut i: usize = 0;
        while i < n {
            if nums[i] == 0 {
                sign = 0;
            } else if nums[i] < 0 {
                sign = sign * -1;
            }
            i += 1;
        }
        sign
    }
}
