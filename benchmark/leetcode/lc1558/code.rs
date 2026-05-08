impl Solution {
    pub fn min_operations(nums: Vec<i32>) -> i32 {
        let mut ones: i32 = 0;
        let mut max_len: i32 = 0;
        let n = nums.len();
        let mut i: usize = 0;
        while i < n {
            let mut val = nums[i];
            let mut bits: i32 = 0;
            let mut len: i32 = 0;
            while val > 0 {
                if val % 2 == 1 {
                    bits = bits + 1;
                }
                val = val / 2;
                len = len + 1;
            }
            ones = ones + bits;
            if len > max_len {
                max_len = len;
            }
            i = i + 1;
        }
        if max_len > 0 {
            ones + max_len - 1
        } else {
            ones
        }
    }
}
