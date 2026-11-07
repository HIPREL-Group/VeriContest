impl Solution {
    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> Vec<i32>
    {
        let n = nums.len();
        let index_difference_usize = index_difference as usize;

        if index_difference_usize >= n {
            let mut result = Vec::new();
            result.push(-1i32);
            result.push(-1i32);
            return result;
        }

        let mut r: usize = index_difference_usize;
        let mut min_idx: usize = 0;
        let mut max_idx: usize = 0;

        while r < n
        {
            let high_gap = nums[max_idx] - nums[r];
            if high_gap >= value_difference {
                let mut result = Vec::new();
                result.push(max_idx as i32);
                result.push(r as i32);
                return result;
            }

            let low_gap = nums[r] - nums[min_idx];
            if low_gap >= value_difference {
                let mut result = Vec::new();
                result.push(min_idx as i32);
                result.push(r as i32);
                return result;
            }

            r = r + 1;
            if r < n {
                let add_idx = r - index_difference_usize;

                if nums[add_idx] < nums[min_idx] {
                    min_idx = add_idx;
                } else {
                }

                if nums[add_idx] > nums[max_idx] {
                    max_idx = add_idx;
                } 
            }
        }

        let mut result = Vec::new();
        result.push(-1i32);
        result.push(-1i32);
        result
    }
}
