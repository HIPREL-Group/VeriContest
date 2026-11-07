impl Solution {
    pub fn max_array_value(nums: Vec<i32>) -> i64 {
        let n = nums.len() as i32;
        let mut cur: i64 = nums[(n - 1) as usize] as i64;
        let mut i: i32 = n - 2;
        while i >= 0 {
            if nums[i as usize] as i64 <= cur {
                cur = cur + nums[i as usize] as i64;
            } else {
                cur = nums[i as usize] as i64;
            }
            i = i - 1;
        }
        cur
    }
}
