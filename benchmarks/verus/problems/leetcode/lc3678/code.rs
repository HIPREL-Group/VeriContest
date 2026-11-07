impl Solution {
    pub fn smallest_absent(nums: Vec<i32>) -> i32 {
        let n_usize = nums.len();
        let n = n_usize as i32;

        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n_usize {
            sum += nums[i];
            i += 1;
        }

        let mut candidate: i32 = 1;
        let mut candidate_times_n: i32 = n;
        while candidate < 101 {
            let mut exists = false;
            let mut j: usize = 0;
            while j < n_usize && !exists {
                if nums[j] == candidate {
                    exists = true;
                }
                j += 1;
            }

            if candidate_times_n > sum && !exists {
                return candidate;
            }
            candidate += 1;
            candidate_times_n += n;
        }

        101
    }
}
