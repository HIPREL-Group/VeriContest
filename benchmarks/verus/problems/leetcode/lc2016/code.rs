impl Solution {
    pub fn maximum_difference(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut min_val: i64 = nums[0] as i64;
        let mut best: i64 = -1;
        let mut i: usize = 1;
        while i < n {
            if nums[i] as i64 > min_val {
                let diff = nums[i] as i64 - min_val;
                if diff > best {
                    best = diff;
                }
            }
            if (nums[i] as i64) < min_val {
                min_val = nums[i] as i64;
            }
            i += 1;
        }
        best as i32
    }
}
