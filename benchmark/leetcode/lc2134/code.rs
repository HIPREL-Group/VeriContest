impl Solution {
    pub fn min_swaps(nums: Vec<i32>) -> i32 {
        let mut total_ones: usize = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] == 1 {
                total_ones = total_ones + 1;
            }
            i = i + 1;
        }
        
        let window_size: usize = total_ones;
        let mut ones_in_window: usize = 0;
        
        i = 0;
        while i < window_size {
            if nums[i] == 1 {
                ones_in_window = ones_in_window + 1;
            }
            i = i + 1;
        }
        
        let mut max_ones = ones_in_window;
        
        let n = nums.len();
        i = 0;
        while i < n {
            if nums[i] == 1 && ones_in_window > 0 {
                ones_in_window = ones_in_window - 1;
            }
            let next_idx = (i + window_size) % n;
            if nums[next_idx] == 1 {
                ones_in_window = ones_in_window + 1;
            }
            if ones_in_window > max_ones {
                max_ones = ones_in_window;
            }
            i = i + 1;
        }
        
        if total_ones >= max_ones {
            (total_ones - max_ones) as i32
        } else {
            0i32
        }
    }
}
