impl Solution {
    pub fn maximum_total_cost(nums: Vec<i32>) -> i64 {
        let n = nums.len();
        let mut add_result = nums[0] as i128;
        let mut sub_result = nums[0] as i128;
        let mut i = 1usize;
        while i < n {
            let best_prev = if add_result >= sub_result { add_result } else { sub_result };
            let x = nums[i] as i128;
            let temp_add = best_prev.checked_add(x).unwrap_or(best_prev);
            let temp_sub = add_result.checked_sub(x).unwrap_or(add_result);
            add_result = temp_add;
            sub_result = temp_sub;
            i += 1;
        }
        let best = if add_result >= sub_result { add_result } else { sub_result };
        best as i64
    }
}
