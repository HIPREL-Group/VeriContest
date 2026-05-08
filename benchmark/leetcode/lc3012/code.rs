impl Solution {
    pub fn minimum_array_length(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut min_v = nums[0] as u64;
        let mut i: usize = 1;
        while i < n {
            let x = nums[i] as u64;
            if x < min_v {
                min_v = x;
            }
            i += 1;
        }

        i = 0;
        while i < n {
            let x = nums[i] as u64;
            if x % min_v != 0 {
                return 1;
            }
            i += 1;
        }

        let mut cnt_min: i32 = 0;
        i = 0;
        while i < n {
            if nums[i] as u64 == min_v {
                cnt_min += 1;
            }
            i += 1;
        }
        (cnt_min + 1) / 2
    }
}
