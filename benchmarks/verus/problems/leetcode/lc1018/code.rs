impl Solution {
    pub fn prefixes_div_by5(nums: Vec<i32>) -> Vec<bool> {
        let mut result: Vec<bool> = Vec::new();
        let mut rem: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            rem = (rem * 2 + nums[i]) % 5;
            result.push(rem == 0);
            i += 1;
        }
        result
    }
}
