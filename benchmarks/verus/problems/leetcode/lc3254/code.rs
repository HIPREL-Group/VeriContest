impl Solution {
    pub fn results_array(nums: Vec<i32>, k: i32) -> Vec<i32> {
        let n = nums.len();
        let k_usize = k as usize;
        let mut result: Vec<i32> = Vec::new();
        let mut run_len: usize = 1;
        if k_usize == 1 {
            result.push(nums[0]);
        }
        let mut i: usize = 1;
        while i < n {
            let prev_val = nums[i - 1];
            let curr_val = nums[i];
            let prev_run_len = run_len;
            if prev_val + 1 == curr_val {
                run_len = prev_run_len + 1;
            } else {
                run_len = 1;
            }
            if i + 1 >= k_usize {
                let out = if run_len >= k_usize { curr_val } else { -1 };
                result.push(out);
            }
            i += 1;
        }
        result
    }
}