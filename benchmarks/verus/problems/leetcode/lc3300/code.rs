impl Solution {
    pub fn min_element(nums: Vec<i32>) -> i32 {
        let mut min_val: i32 = i32::MAX;
        for i in 0..nums.len() {
            let mut s: u32 = 0;
            let mut x: u32 = nums[i] as u32;
            while x > 0 {
                let d = x % 10;
                s += d;
                x = x / 10;
            }
            if i == 0 || (s as i32) < min_val {
                min_val = s as i32;
            }
        }
        min_val
    }
}
