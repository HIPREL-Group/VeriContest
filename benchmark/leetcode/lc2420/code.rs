impl Solution {
    pub fn good_indices(nums: Vec<i32>, k: i32) -> Vec<i32> {
        let n = nums.len();
        let k_usize = k as usize;

        let mut inc_prefix: Vec<i32> = Vec::new();
        let mut dec_prefix: Vec<i32> = Vec::new();
        inc_prefix.push(0);
        dec_prefix.push(0);

        let mut i: usize = 1;
        while i < n {
            let prev = nums[i - 1];
            let curr = nums[i];

            let mut inc_next = inc_prefix[i - 1];
            if prev < curr {
                inc_next += 1;
            }

            let mut dec_next = dec_prefix[i - 1];
            if prev > curr {
                dec_next += 1;
            }

            inc_prefix.push(inc_next);
            dec_prefix.push(dec_next);
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut idx = k_usize;
        while idx + k_usize < n {
            let idx_i = idx as i32;
            if inc_prefix[idx - 1] == inc_prefix[idx - k_usize]
                && dec_prefix[idx + k_usize] == dec_prefix[idx + 1]
            {
                result.push(idx_i);
            }
            idx += 1;
        }

        result
    }
}
