impl Solution {
    pub fn ways_to_make_fair(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut right_even: i64 = 0;
        let mut right_odd: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 {
                right_even = right_even + nums[i] as i64;
            } else {
                right_odd = right_odd + nums[i] as i64;
            }
            i = i + 1;
        }
        let mut left_even: i64 = 0;
        let mut left_odd: i64 = 0;
        let mut result: i32 = 0;
        i = 0;
        while i < n {
            if i % 2 == 0 {
                right_even = right_even - nums[i] as i64;
            } else {
                right_odd = right_odd - nums[i] as i64;
            }
            if left_even + right_odd == left_odd + right_even {
                result = result + 1;
            }
            if i % 2 == 0 {
                left_even = left_even + nums[i] as i64;
            } else {
                left_odd = left_odd + nums[i] as i64;
            }
            i = i + 1;
        }
        result
    }
}
