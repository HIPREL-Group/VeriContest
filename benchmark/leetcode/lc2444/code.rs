impl Solution {
    pub fn count_subarrays(nums: Vec<i32>, min_k: i32, max_k: i32) -> i64 {
        let n = nums.len();
        let mut result: i64 = 0;
        let mut last_bad: i64 = -1;
        let mut last_min: i64 = -1;
        let mut last_max: i64 = -1;
        let mut i: usize = 0;

        while i < n {
            let value = nums[i];
            if value < min_k || value > max_k {
                last_bad = i as i64;
            }
            if value == min_k {
                last_min = i as i64;
            }
            if value == max_k {
                last_max = i as i64;
            }
            let bound = if last_min < last_max {
                last_min
            } else {
                last_max
            };
            let add = if bound > last_bad { bound - last_bad } else { 0 };
            result = result + add;
            i = i + 1;
        }

        result
    }
}
